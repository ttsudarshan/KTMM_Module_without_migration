/*
 *  ktmm_vmscan.c
 *
 *  Page scanning and related functions with allocation tracking.
 */

 #include <linux/atomic.h>
 #include <linux/bitops.h>
 #include <linux/buffer_head.h>
 #include <linux/cgroup.h>
 #include <linux/delay.h>
 #include <linux/freezer.h>
 #include <linux/fs.h>
 #include <linux/gfp.h>
 #include <linux/hashtable.h>
 #include <linux/kernel.h>
 #include <linux/kprobes.h>
 #include <linux/kthread.h>
 #include <linux/list.h>
 #include <linux/module.h>
 #include <linux/memcontrol.h>
 #include <linux/mmzone.h>
 #include <linux/mm_inline.h>
 #include <linux/migrate.h>
 #include <linux/migrate_mode.h>
 #include <linux/nodemask.h>
 #include <linux/numa.h>
 #include <linux/page-flags.h>
 #include <linux/page_ref.h>
 #include <linux/pagemap.h>
 #include <linux/pagevec.h>
 #include <linux/printk.h>
 #include <linux/rmap.h>
 #include <linux/signal.h>
 #include <linux/sched.h>
 #include <linux/spinlock.h>
 #include <linux/swap.h>
 #include <linux/vmstat.h>
 #include <linux/wait.h>
 
 #include "ktmm_hook.h"
 #include "ktmm_vmscan.h"
 
 #define TMEMD_GFP_FLAGS GFP_NOIO
 
 /* Page allocation tracking structure */
 typedef struct {
   unsigned long dram_pages;
   unsigned long pm_pages;
   unsigned long total_pages;
   spinlock_t lock;
 } page_stats_t;
 
 /* Global statistics for each node */
 static page_stats_t node_stats[MAX_NUMNODES];
 
 int pmem_node = -1;
 
 static struct task_struct *tmemd_list[MAX_NUMNODES];
 
 wait_queue_head_t tmemd_wait[MAX_NUMNODES];
 
 /************** PAGE ALLOCATION TRACKING FUNCTIONS *****************************/
 
 /**
  * init_page_stats - Initialize page statistics for all nodes
  */
 static void init_page_stats(void)
 {
   int i;
   for (i = 0; i < MAX_NUMNODES; i++) {
     spin_lock_init(&node_stats[i].lock);
     node_stats[i].dram_pages = 0;
     node_stats[i].pm_pages = 0;
     node_stats[i].total_pages = 0;
   }
   printk(KERN_INFO "KTMM: Page statistics initialized for %d nodes\n", MAX_NUMNODES);
 }
 
 /**
  * update_page_allocation - Update allocation statistics for a page/folio
  *
  * @folio:	folio being allocated
  * @nid:	node ID where folio resides
  * @is_pmem:	true if page is on persistent memory
  */
 static void update_page_allocation(struct folio *folio, int nid, bool is_pmem)
 {
   unsigned long folio_pages = folio_nr_pages(folio);
 
   if (nid < 0 || nid >= MAX_NUMNODES)
     return;
 
   spin_lock(&node_stats[nid].lock);
 
   if (is_pmem) {
     node_stats[nid].pm_pages += folio_pages;
   } else {
     node_stats[nid].dram_pages += folio_pages;
   }
   node_stats[nid].total_pages += folio_pages;
 
   spin_unlock(&node_stats[nid].lock);
 }
 
 /**
  * print_node_allocation_stats - Print detailed allocation statistics
  *
  * @nid:	node ID to print stats for
  * @context:	context string for logging
  */
 static void print_node_allocation_stats(int nid, const char *context)
 {
   unsigned long dram, pm, total;
 
   if (nid < 0 || nid >= MAX_NUMNODES)
     return;
 
   spin_lock(&node_stats[nid].lock);
 
   dram = node_stats[nid].dram_pages;
   pm = node_stats[nid].pm_pages;
   total = node_stats[nid].total_pages;
 
   spin_unlock(&node_stats[nid].lock);
 
   printk(KERN_INFO "KTMM: [%s] Node %d - DRAM: %lu pages, PM: %lu pages, "
     "Total: %lu pages (DRAM: %lu%%, PM: %lu%%)\n",
     context, nid, dram, pm, total,
     total > 0 ? (dram * 100) / total : 0,
     total > 0 ? (pm * 100) / total : 0);
 }
 
 /**
  * get_folio_node - Determine if folio is on DRAM or PM
  *
  * @folio:	folio to check
  * @nid:	output parameter for node ID
  *
  * @returns:	true if on PM, false if on DRAM
  */
 static bool get_folio_node(struct folio *folio, int *nid)
 {
   int folio_nid = folio_nid_valid(folio) ? page_to_nid(&folio->page) : -1;
   
   if (folio_nid < 0)
     return false;
 
   *nid = folio_nid;
 
   /* Check if this node is marked as PM node */
   if (folio_nid == pmem_node)
     return true;
 
   return false;
 }
 
 /************** MISC HOOKED FUNCTION PROTOTYPES *****************************/
 static struct mem_cgroup *(*pt_mem_cgroup_iter)(struct mem_cgroup *root,
       struct mem_cgroup *prev,
       struct mem_cgroup_reclaim_cookie *reclaim);
 
 static bool (*pt_zone_watermark_ok_safe)(struct zone *z,
         unsigned int order,
         unsigned long mark,
         int highest_zoneidx);
 
 static struct pglist_data *(*pt_first_online_pgdat)(void);
 
 static struct zone *(*pt_next_zone)(struct zone *zone);
 
 static void (*pt_free_unref_page_list)(struct list_head *list);
 
 static void (*pt_lru_add_drain)(void);
 
 static void (*pt_cgroup_update_lru_size)(struct lruvec *lruvec, enum lru_list lru,
         int zid, int nr_pages);
 
 static void (*pt_cgroup_uncharge_list)(struct list_head *page_list);
 
 static unsigned long (*pt_isolate_lru_folios)(unsigned long nr_to_scan, struct lruvec *lruvec,
         struct list_head *dst, unsigned long *nr_scanned,
         struct scan_control *sc, enum lru_list lru);
 
 static unsigned int (*pt_move_folios_to_lru)(struct lruvec *lruvec, struct list_head *list);
 
 static void (*pt_folio_putback_lru)(struct folio *folio);
 
 static int (*pt_folio_referenced)(struct folio *folio, int is_locked,
       struct mem_cgroup *memcg, unsigned long *vm_flags);
 
 static struct page *(*pt_alloc_pages)(gfp_t gfp_mask, unsigned int order, int preferred_nid,
         nodemask_t *nodemask);
 
 /**************** KTMM IMPLEMENTATION OF HOOKED FUNCTION **********************/
 static struct mem_cgroup *ktmm_mem_cgroup_iter(struct mem_cgroup *root,
       struct mem_cgroup *prev,
       struct mem_cgroup_reclaim_cookie *reclaim)
 {
   return pt_mem_cgroup_iter(root, prev, reclaim);
 }
 
 static bool ktmm_zone_watermark_ok_safe(struct zone *z,
         unsigned int order,
         unsigned long mark,
         int highest_zoneidx)
 {
   return pt_zone_watermark_ok_safe(z, order, mark, highest_zoneidx);
 }
 
 static struct pglist_data *ktmm_first_online_pgdat(void)
 {
   return pt_first_online_pgdat();
 }
 
 static struct zone *ktmm_next_zone(struct zone *zone)
 {
   return pt_next_zone(zone);
 }
 
 static void ktmm_free_unref_page_list(struct list_head *list)
 {
   return pt_free_unref_page_list(list);
 }
 
 static void ktmm_lru_add_drain(void)
 {
   pt_lru_add_drain();
 }
 
 static void ktmm_cgroup_update_lru_size(struct lruvec *lruvec, enum lru_list lru,
         int zid, int nr_pages)
 {
   pt_cgroup_update_lru_size(lruvec, lru, zid, nr_pages);
 }
 
 static void ktmm_cgroup_uncharge_list(struct list_head *page_list)
 {
   pt_cgroup_uncharge_list(page_list);
 }
 
 static unsigned long ktmm_isolate_lru_folios(unsigned long nr_to_scan, struct lruvec *lruvec,
         struct list_head *dst, unsigned long *nr_scanned,
         struct scan_control *sc, enum lru_list lru)
 {
   return pt_isolate_lru_folios(nr_to_scan, lruvec, dst, nr_scanned, sc, lru);
 }
 
 static unsigned int ktmm_move_folios_to_lru(struct lruvec *lruvec, struct list_head *list)
 {
   return pt_move_folios_to_lru(lruvec, list);
 }
 
 static void ktmm_folio_putback_lru(struct folio *folio)
 {
   pt_folio_putback_lru(folio);
 }
 
 static int ktmm_folio_referenced(struct folio *folio, int is_locked,
       struct mem_cgroup *memcg, unsigned long *vm_flags)
 {
   return pt_folio_referenced(folio, is_locked, memcg, vm_flags);
 }
 
 /*****************************************************************************
  * ALLOC & SWAP
  *****************************************************************************/
 
 struct page* alloc_pmem_page(struct page *page, unsigned long data)
 {
   gfp_t gfp_mask = GFP_USER | __GFP_PMEM;
   return alloc_page(gfp_mask);
 }
 
 struct page* alloc_normal_page(struct page *page, unsigned long data)
 {
   gfp_t gfp_mask = GFP_USER;
   return alloc_page(gfp_mask);
 }
 
 static struct page *ktmm_alloc_pages(gfp_t gfp_mask, unsigned int order, int preferred_nid,
         nodemask_t *nodemask)
 {
   nodemask_t nodemask_test;
   int nid;
   
   if ((gfp_mask & __GFP_PMEM) != 0) {
     for_each_node_state(nid, N_MEMORY) {
       if(NODE_DATA(nid)->pm_node != 0)
         node_set(nid, nodemask_test);
       else
         node_clear(nid, nodemask_test);
     }
     nodemask = &nodemask_test;
   }
   else if ((gfp_mask & __GFP_PMEM) == 0 && pmem_node_id != -1) {
     for_each_node_state(nid, N_MEMORY) {
       if (NODE_DATA(nid)->pm_node == 0)
         node_set(nid, nodemask_test);
       else
         node_clear(nid, nodemask_test);
     }
     nodemask = &nodemask_test;
   }
   return pt_alloc_pages(gfp_mask, order, preferred_nid, nodemask);
 }
 
 /*****************************************************************************
  * Node Scanning with Allocation Tracking
  *****************************************************************************/
 
 static bool ktmm_cgroup_below_low(struct mem_cgroup *memcg)
 {
   return READ_ONCE(memcg->memory.elow) >=
     page_counter_read(&memcg->memory);
 }
 
 static bool ktmm_cgroup_below_min(struct mem_cgroup *memcg)
 {
   return READ_ONCE(memcg->memory.emin) >=
     page_counter_read(&memcg->memory);
 }
 
 static __always_inline void ktmm_update_lru_sizes(struct lruvec *lruvec,
     enum lru_list lru, unsigned long *nr_zone_taken)
 {
   int zid;
 
   for (zid = 0; zid < MAX_NR_ZONES; zid++) {
     if (!nr_zone_taken[zid])
       continue;
 
     ktmm_cgroup_update_lru_size(lruvec, lru, zid, -nr_zone_taken[zid]);
   }
 }
 
 static inline bool ktmm_folio_evictable(struct folio *folio)
 {
   bool ret;
 
   rcu_read_lock();
   ret = !mapping_unevictable(folio_mapping(folio)) &&
     !folio_test_mlocked(folio);
   rcu_read_unlock();
   return ret;
 }
 
 static inline bool ktmm_folio_needs_release(struct folio *folio)
 {
   struct address_space *mapping = folio_mapping(folio);
 
   return folio_has_private(folio) || (mapping && mapping_release_always(mapping));
 }
 
 /**
  * scan_promote_list - scan promote lru folios with allocation tracking
  */
 static void scan_promote_list(unsigned long nr_to_scan,
       struct lruvec *lruvec,
       struct scan_control *sc,
       enum lru_list lru,
       struct pglist_data *pgdat)
 {
   unsigned long nr_taken;
   unsigned long nr_scanned;
   unsigned long nr_migrated = 0;
   unsigned long dram_count = 0, pm_count = 0;
   isolate_mode_t isolate_mode = 0;
   LIST_HEAD(l_hold);
   int file = is_file_lru(lru);
   int nid = pgdat->node_id;
   struct list_head *src = &lruvec->lists[lru];
   struct folio *folio;
 
   if (list_empty(src))
     pr_debug("promote list empty");
 
   if (!sc->may_unmap)
     isolate_mode |= ISOLATE_UNMAPPED;
 
   ktmm_lru_add_drain();
 
   spin_lock_irq(&lruvec->lru_lock);
 
   nr_taken = ktmm_isolate_lru_folios(nr_to_scan, lruvec, &l_hold,
         &nr_scanned, sc, lru);
   __mod_node_page_state(pgdat, NR_ISOLATED_ANON + file, nr_taken);
 
   spin_unlock_irq(&lruvec->lru_lock);
 
   /* Count pages on promote list */
   list_for_each_entry(folio, &l_hold, lru) {
     int folio_nid;
     bool is_pm = get_folio_node(folio, &folio_nid);
     if (is_pm)
       pm_count += folio_nr_pages(folio);
     else
       dram_count += folio_nr_pages(folio);
   }
 
   printk(KERN_INFO "KTMM: [scan_promote_list] Node %d - Scanned: %lu, "
     "Taken: %lu (DRAM: %lu, PM: %lu)\n",
     nid, nr_scanned, nr_taken, dram_count, pm_count);
 
   if (nr_taken) {
     nr_migrated = 0;
     pr_debug("pgdat %d MIGRATION DISABLED - would have migrated %lu folios from promote list", nid, nr_taken);
   }
 
   spin_lock_irq(&lruvec->lru_lock);
 
   ktmm_move_folios_to_lru(lruvec, &l_hold);
   __mod_node_page_state(pgdat, NR_ISOLATED_ANON + file, -nr_taken);
 
   spin_unlock_irq(&lruvec->lru_lock);
 
   ktmm_cgroup_uncharge_list(&l_hold);
   ktmm_free_unref_page_list(&l_hold);
 }
 
 /**
  * scan_active_list - scan active lru folios with allocation tracking
  */
 static void scan_active_list(unsigned long nr_to_scan,
       struct lruvec *lruvec,
       struct scan_control *sc,
       enum lru_list lru,
       struct pglist_data *pgdat)
 {
   unsigned long nr_taken;
   unsigned long nr_scanned;
   unsigned long vm_flags;
   unsigned long dram_count = 0, pm_count = 0;
   LIST_HEAD(l_hold);
   LIST_HEAD(l_active);
   LIST_HEAD(l_inactive);
   LIST_HEAD(l_promote);
   unsigned nr_deactivate, nr_activate, nr_promote;
   unsigned nr_rotated = 0;
   int file = is_file_lru(lru);
   int nid = pgdat->node_id;
 
   ktmm_lru_add_drain();
 
   spin_lock_irq(&lruvec->lru_lock);
 
   nr_taken = ktmm_isolate_lru_folios(nr_to_scan, lruvec, &l_hold,
            &nr_scanned, sc, lru);
 
   __mod_node_page_state(pgdat, NR_ISOLATED_ANON + file, nr_taken);
 
   spin_unlock_irq(&lruvec->lru_lock);
 
   while (!list_empty(&l_hold)) {
     struct folio *folio;
     int folio_nid;
     bool is_pm;
 
     cond_resched();
     folio = lru_to_folio(&l_hold);
     list_del(&folio->lru);
 
     is_pm = get_folio_node(folio, &folio_nid);
     if (is_pm)
       pm_count += folio_nr_pages(folio);
     else
       dram_count += folio_nr_pages(folio);
 
     if (unlikely(!ktmm_folio_evictable(folio))) {
       ktmm_folio_putback_lru(folio);
       continue;
     }
 
     if (unlikely(buffer_heads_over_limit)) {
       if (ktmm_folio_needs_release(folio) &&
           folio_trylock(folio)) {
         filemap_release_folio(folio, 0);
         folio_unlock(folio);
       }
     }
 
     if (pgdat->pm_node != 0) {
       if (ktmm_folio_referenced(folio, 0, sc->target_mem_cgroup, &vm_flags)) {
         pr_debug("set promote");
         folio_set_promote(folio);
         list_add(&folio->lru, &l_promote);
         continue;
       }
     }
 
     if (ktmm_folio_referenced(folio, 0, sc->target_mem_cgroup,
            &vm_flags) != 0) {
       if ((vm_flags & VM_EXEC) && folio_is_file_lru(folio)) {
         nr_rotated += folio_nr_pages(folio);
         list_add(&folio->lru, &l_active);
         continue;
       }
     }
 
     folio_clear_active(folio);
     folio_set_workingset(folio);
     list_add(&folio->lru, &l_inactive);
   }
 
   spin_lock_irq(&lruvec->lru_lock);
 
   nr_activate = ktmm_move_folios_to_lru(lruvec, &l_active);
   nr_deactivate = ktmm_move_folios_to_lru(lruvec, &l_inactive);
   nr_promote = ktmm_move_folios_to_lru(lruvec, &l_promote);
 
   pr_debug("pgdat %d folio activated: %d", nid, nr_activate);
   pr_debug("pgdat %d folio deactivated: %d", nid, nr_deactivate);
   pr_debug("pgdat %d folio promoted: %d", nid, nr_promote);
 
   list_splice(&l_inactive, &l_active);
 
   __mod_node_page_state(pgdat, NR_ISOLATED_ANON + file, -nr_taken);
 
   spin_unlock_irq(&lruvec->lru_lock);
 
   printk(KERN_INFO "KTMM: [scan_active_list] Node %d - Scanned: %lu, "
     "Taken: %lu (DRAM: %lu, PM: %lu) | Activated: %u, Deactivated: %u, Promoted: %u\n",
     nid, nr_scanned, nr_taken, dram_count, pm_count, 
     nr_activate, nr_deactivate, nr_promote);
 
   ktmm_cgroup_uncharge_list(&l_active);
   ktmm_free_unref_page_list(&l_active);
 }
 
 /**
  * scan_inactive_list - scan inactive lru list with allocation tracking
  */
 static unsigned long scan_inactive_list(unsigned long nr_to_scan,
         struct lruvec *lruvec,
         struct scan_control *sc,
         enum lru_list lru,
         struct pglist_data *pgdat)
 {
   LIST_HEAD(folio_list);
   unsigned long nr_scanned;
   unsigned long nr_taken = 0;
   unsigned long nr_migrated = 0;
   unsigned long nr_reclaimed = 0;
   unsigned long dram_count = 0, pm_count = 0;
   bool file = is_file_lru(lru);
   int nid = pgdat->node_id;
   struct folio *folio;
 
   ktmm_lru_add_drain();
 
   spin_lock_irq(&lruvec->lru_lock);
 
   nr_taken = ktmm_isolate_lru_folios(nr_to_scan, lruvec, &folio_list,
            &nr_scanned, sc, lru);
 
   __mod_node_page_state(pgdat, NR_ISOLATED_ANON + file, nr_taken);
 
   spin_unlock_irq(&lruvec->lru_lock);
 
   if (nr_taken == 0) return 0;
 
   /* Count pages on inactive list */
   list_for_each_entry(folio, &folio_list, lru) {
     int folio_nid;
     bool is_pm = get_folio_node(folio, &folio_nid);
     if (is_pm)
       pm_count += folio_nr_pages(folio);
     else
       dram_count += folio_nr_pages(folio);
   }
 
   if (pgdat->pm_node == 0 && pmem_node_id != -1) {
     nr_migrated = 0;
     pr_debug("pgdat %d MIGRATION DISABLED - would have migrated %lu folios from inactive list", nid, nr_taken);
   }
 
   spin_lock_irq(&lruvec->lru_lock);
 
   ktmm_move_folios_to_lru(lruvec, &folio_list);
   __mod_node_page_state(pgdat, NR_ISOLATED_ANON + file, -nr_taken);
 
   spin_unlock_irq(&lruvec->lru_lock);
 
   printk(KERN_INFO "KTMM: [scan_inactive_list] Node %d - Scanned: %lu, "
     "Taken: %lu (DRAM: %lu, PM: %lu)\n",
     nid, nr_scanned, nr_taken, dram_count, pm_count);
 
   ktmm_cgroup_uncharge_list(&folio_list);
   ktmm_free_unref_page_list(&folio_list);
 
   return nr_migrated;
 }
 
 static unsigned long scan_list(enum lru_list lru, 
       unsigned long nr_to_scan,
       struct lruvec *lruvec, 
       struct scan_control *sc,
       struct pglist_data *pgdat)
 {
   if (is_active_lru(lru))
     scan_active_list(nr_to_scan, lruvec, sc, lru, pgdat);
 
   if(is_promote_lru(lru))
     scan_promote_list(nr_to_scan, lruvec, sc, lru, pgdat);
 
   return scan_inactive_list(nr_to_scan, lruvec, sc, lru, pgdat);
 }
 
 /**
  * scan_node - scan a node's LRU lists with detailed statistics
  */
 static void scan_node(pg_data_t *pgdat, 
     struct scan_control *sc,
     struct mem_cgroup_reclaim_cookie *reclaim)
 {
   enum lru_list lru;
   struct mem_cgroup *memcg;
   int nid = pgdat->node_id;
   int memcg_count;
 
   printk(KERN_INFO "KTMM: ===== Beginning node %d scan =====\n", nid);
   print_node_allocation_stats(nid, "scan_node_start");
 
   memset(&sc->nr, 0, sizeof(sc->nr));
   memcg = ktmm_mem_cgroup_iter(NULL, NULL, reclaim);
   sc->target_mem_cgroup = memcg;
 
   memcg_count = 0;
   do {
     struct lruvec *lruvec = &memcg->nodeinfo[nid]->lruvec;
     unsigned long reclaimed;
     unsigned long scanned;
 
     memcg_count += 1;
 
     if (ktmm_cgroup_below_min(memcg)) {
       continue;
     } else if (ktmm_cgroup_below_low(memcg)) {
       if (!sc->memcg_low_reclaim) {
         sc->memcg_low_skipped = 1;
         continue;
       }
     }
 
     reclaimed = sc->nr_reclaimed;
     scanned = sc->nr_scanned;
 
     for_each_evictable_lru(lru) {
       unsigned long nr_to_scan = 32;
 
       scan_list(lru, nr_to_scan, lruvec, sc, pgdat);
     }
   } while ((memcg = ktmm_mem_cgroup_iter(NULL, memcg, NULL)));
 
   print_node_allocation_stats(nid, "scan_node_end");
   printk(KERN_INFO "KTMM: ===== Completed node %d scan =====\n\n", nid);
 }
 
 /*****************************************************************************
  * Daemon Functions & Related
  *****************************************************************************/
 
 static void tmemd_try_to_sleep(pg_data_t *pgdat, int nid)
 {
   long remaining = 0;
   DEFINE_WAIT(wait);
 
   if (freezing(current) || kthread_should_stop())
     return;
   
   prepare_to_wait(&tmemd_wait[nid], &wait, TASK_INTERRUPTIBLE);
   remaining = schedule_timeout(HZ);
 
   finish_wait(&tmemd_wait[nid], &wait);
 }
 
 static int tmemd(void *p) 
 {
   pg_data_t *pgdat = (pg_data_t *)p;
   int nid = pgdat->node_id;
   struct task_struct *task = current;
   const struct cpumask *cpumask = cpumask_of_node(nid);
 
   struct mem_cgroup_reclaim_cookie reclaim = {
     .pgdat = pgdat,
   };
 
   struct reclaim_state reclaim_state = {
     .reclaimed_slab = 0,
   };
 
   struct scan_control sc = {
     .nr_to_reclaim = SWAP_CLUSTER_MAX,
     .priority = DEF_PRIORITY,
     .may_writepage = !laptop_mode,
     .may_unmap = 1,
     .may_swap = 1,
     .reclaim_idx = MAX_NR_ZONES - 1,
     .only_promote = 1,
   };
 
   if(!cpumask_empty(cpumask))
     set_cpus_allowed_ptr(task, cpumask);
 
   current->reclaim_state = &reclaim_state;
 
   task->flags |= PF_MEMALLOC | PF_KSWAPD;
 
   printk(KERN_INFO "KTMM: tmemd daemon started on node %d\n", nid);
 
   for ( ; ; )
   {
     scan_node(pgdat, &sc, &reclaim);
 
     if (kthread_should_stop()) break;
 
     tmemd_try_to_sleep(pgdat, nid);
   }
 
   task->flags &= ~(PF_MEMALLOC | PF_KSWAPD);
   current->reclaim_state = NULL;
   
   printk(KERN_INFO "KTMM: tmemd daemon stopped on node %d\n", nid);
   
   return 0;
 }
 
 /*****************************************************************************
  * Start & Stop
  *****************************************************************************/
 
 static struct ktmm_hook vmscan_hooks[] = {
   HOOK("mem_cgroup_iter", ktmm_mem_cgroup_iter, &pt_mem_cgroup_iter),
   HOOK("zone_watermark_ok", ktmm_zone_watermark_ok_safe, &pt_zone_watermark_ok_safe),
   HOOK("first_online_pgdat", ktmm_first_online_pgdat, &pt_first_online_pgdat),
   HOOK("next_zone", ktmm_next_zone, &pt_next_zone),
   HOOK("free_unref_page_list", ktmm_free_unref_page_list, &pt_free_unref_page_list),
   HOOK("lru_add_drain", ktmm_lru_add_drain, &pt_lru_add_drain),
   HOOK("mem_cgroup_update_lru_size", ktmm_cgroup_update_lru_size, &pt_cgroup_update_lru_size),
   HOOK("__mem_cgroup_uncharge_list", ktmm_cgroup_uncharge_list, &pt_cgroup_uncharge_list),
   HOOK("isolate_lru_folios", ktmm_isolate_lru_folios, &pt_isolate_lru_folios),
   HOOK("move_folios_to_lru", ktmm_move_folios_to_lru, &pt_move_folios_to_lru),
   HOOK("folio_putback_lru", ktmm_folio_putback_lru, &pt_folio_putback_lru),
   HOOK("folio_referenced", ktmm_folio_referenced, &pt_folio_referenced),
   HOOK("__alloc_pages", ktmm_alloc_pages, &pt_alloc_pages),
 };
 
 /**
  * tmemd_start_available - Start tmemd daemons on all online nodes
  *
  * Initializes page statistics and installs hooks on all online nodes.
  * Emulates node 1 as the persistent memory node.
  */
 int tmemd_start_available(void) 
 {
   int i;
   int nid;
   int ret;
 
   /* Initialize page allocation tracking */
   init_page_stats();
 
   set_ktmm_scan();
 
   /* Initialize wait queues for sleeping */
   for (i = 0; i < MAX_NUMNODES; i++)
     init_waitqueue_head(&tmemd_wait[i]);
 
   ret = install_hooks(vmscan_hooks, ARRAY_SIZE(vmscan_hooks));
   
   for_each_online_node(nid)
   {
     pg_data_t *pgdat = NODE_DATA(nid);
 
     /* !! EMULATE PMEM NODE !! */
     if (nid == 1) {
       printk(KERN_INFO "KTMM: Emulating pmem node\n");
       set_pmem_node_id(nid);
       set_pmem_node(nid);
       pmem_node = nid;
     }
 
           tmemd_list[nid] = kthread_run(&tmemd, pgdat, "tmemd");
     printk(KERN_INFO "KTMM: Started tmemd on node %d\n", nid);
   }
 
   printk(KERN_INFO "KTMM: Module initialized successfully\n");
   return ret;
 }
 
 /**
  * tmemd_stop_all - Stop all tmemd daemons and uninstall hooks
  *
  * Gracefully stops all running daemons and removes kernel hooks.
  */
 void tmemd_stop_all(void)
 {
   int nid;
 
   printk(KERN_INFO "KTMM: Stopping all tmemd daemons...\n");
 
   for_each_online_node(nid)
   {
     if (tmemd_list[nid]) {
       kthread_stop(tmemd_list[nid]);
       printk(KERN_INFO "KTMM: Stopped tmemd on node %d\n", nid);
     }
   }
 
   uninstall_hooks(vmscan_hooks, ARRAY_SIZE(vmscan_hooks));
   
   printk(KERN_INFO "KTMM: Module cleanup completed\n");
 }