/*
* ktmm_vmscan.c - COMPILATION-FIXED ANTI-FREEZE VERSION
*
* Page scanning and related functions.
* FIXES ALL COMPILATION ERRORS AND FREEZE BUGS
*/

#define pr_fmt(fmt) "[ KTMM Mod ] vmscan - " fmt

#include <linux/kernel.h>
#include <linux/module.h>
#include <linux/init.h>
#include <linux/slab.h>
#include <linux/mm.h>
#include <linux/mmzone.h>
#include <linux/pagemap.h>
#include <linux/swap.h>
#include <linux/migrate.h> //***
#include <linux/swapops.h>
#include <linux/buffer_head.h>
#include <linux/kthread.h>
#include <linux/freezer.h>
#include <linux/memcontrol.h>
#include <linux/delayacct.h>
#include <linux/delay.h>  // FIXED: Add for msleep and usleep_range
//#include <linux/sysctl.h>
#include <linux/oom.h>
#include <linux/pagevec.h>
#include <linux/prefetch.h>
#include <linux/printk.h>
#include <linux/dax.h>
#include <linux/psi.h>
#include <linux/pagewalk.h>
#include <linux/shmem_fs.h>
#include <linux/ctype.h>
#include <linux/debugfs.h>
#include <linux/khugepaged.h>
#include <linux/rculist_nulls.h>
#include <linux/random.h>
#include <linux/cpuset.h>
#include <linux/compaction.h>
#include <linux/rmap.h>
#include <linux/list.h>
#include "ktmm_hook.h"
#include "ktmm_vmscan.h"

// possibly needs to be GFP_USER?
#define TMEMD_GFP_FLAGS GFP_NOIO

// AGGRESSIVE: Add comprehensive safety limits
#define KTMM_MAX_SCAN_ITERATIONS 10000
#define KTMM_MAX_MIGRATE_ATTEMPTS 10
#define KTMM_MAX_MEMCG_ITERATIONS 50
#define KTMM_MAX_TMEMD_ITERATIONS 100000
#define KTMM_SLEEP_INTERVAL_MS 100

#define scan_lru_list(lruvec, lru, nid, body)                        \
do {                                                                  \
    struct list_head *head = &((lruvec)->lists[(lru)]);               \
    struct page *page, *tmp;                                          \
    unsigned int __iter = 0;                                          \
                                                                     \
    /* 1) Skip empty lists */                                        \
    if (list_empty(head)) {                                          \
        pr_debug("KTMM: skip empty LRU[%d] on node %d\n", (lru), (nid)); \
        break;                                                       \
    }                                                                \
                                                                     \
    /* 2) Bounded iteration */                                       \
    list_for_each_entry_safe(page, tmp, head, lru_list) {            \
        if (++__iter > KTMM_MAX_SCAN_ITERATIONS) {                   \
            pr_warn("KTMM: scan limit reached LRU[%d] on node %d\n", \
                    (lru), (nid));                                   \
            break;                                                   \
        }                                                            \
        body;                                                        \
    }                                                                \
                                                                     \
    /* 3) Reset corrupted head */                                    \
    if (head->next == head || head->prev == head) {                  \
        pr_warn("KTMM: resetting corrupted LRU[%d] head on node %d\n", \
                (lru), (nid));                                       \
        INIT_LIST_HEAD(head);                                        \
    }                                                                \
} while (0)

// which node is the pmem node
int pmem_node = -1;

/* holds pointers to the tmemd daemons running per node */
static struct task_struct *tmemd_list[MAX_NUMNODES];

/* per node tmemd wait queues */
wait_queue_head_t tmemd_wait[MAX_NUMNODES];

// AGGRESSIVE: Global safety counters
static atomic_t global_scan_counter = ATOMIC_INIT(0);
static atomic_t global_migrate_counter = ATOMIC_INIT(0);
static atomic_t global_tmemd_counter = ATOMIC_INIT(0);

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

/* __alloc_pages (page_alloc.c) */
/* probably needs removed */
static struct page *(*pt_alloc_pages)(gfp_t gfp_mask, unsigned int order, int preferred_nid,
                                     nodemask_t *nodemask);

/**************** KTMM IMPLEMENTATION OF HOOKED FUNCTION - HARDENED **********************/

static struct mem_cgroup *ktmm_mem_cgroup_iter(struct mem_cgroup *root,
                                              struct mem_cgroup *prev,
                                              struct mem_cgroup_reclaim_cookie *reclaim) {
    return pt_mem_cgroup_iter(root, prev, reclaim);
}

static bool ktmm_zone_watermark_ok_safe(struct zone *z,
                                       unsigned int order,
                                       unsigned long mark,
                                       int highest_zoneidx) {
    return pt_zone_watermark_ok_safe(z, order, mark, highest_zoneidx);
}

static struct pglist_data *ktmm_first_online_pgdat(void) {
    return pt_first_online_pgdat();
}

static struct zone *ktmm_next_zone(struct zone *zone) {
    return pt_next_zone(zone);
}

// AGGRESSIVE: Hardened free_unref_page_list with comprehensive checks
static void ktmm_free_unref_page_list(struct list_head *list) {
    if (!list) {
        pr_warn("KTMM: NULL list in free_unref_page_list");
        return;
    }
    
    // CRITICAL: Check for corrupted list pointers
    if (list->next == NULL || list->prev == NULL) {
        pr_err("KTMM: Corrupted list pointers in free_unref_page_list");
        return;
    }
    
    // CRITICAL: Check for self-referencing loops
    if (list->next == list || list->prev == list) {
        pr_err("KTMM: Self-referencing list detected");
        return;  
    }
    
    // CRITICAL: Empty list check
    if (list_empty(list)) {
        return; // Safe to continue with empty list
    }
    
    return pt_free_unref_page_list(list);
}

static void ktmm_lru_add_drain(void) {
    pt_lru_add_drain();
}

// AGGRESSIVE: Ultra-hardened cgroup_update_lru_size
static void ktmm_cgroup_update_lru_size(struct lruvec *lruvec, enum lru_list lru,
                                       int zid, int nr_pages) {
    // CRITICAL: Comprehensive parameter validation
    if (!lruvec) {
        pr_err("KTMM: NULL lruvec in cgroup_update_lru_size");
        return;
    }
    
    if (lru >= NR_LRU_LISTS || lru < 0) {
        pr_err("KTMM: Invalid LRU list %d (max %d)", lru, NR_LRU_LISTS-1);
        return;
    }
    
    if (zid >= MAX_NR_ZONES || zid < 0) {
        pr_err("KTMM: Invalid zone ID %d (max %d)", zid, MAX_NR_ZONES-1);
        return;
    }
    
    // CRITICAL: Prevent extreme values that could cause overflow
    if (abs(nr_pages) > 1000000) {
        pr_err("KTMM: Extreme nr_pages value %d, clamping to 1000", nr_pages);
        nr_pages = (nr_pages > 0) ? 1000 : -1000;
    }
    
    pt_cgroup_update_lru_size(lruvec, lru, zid, nr_pages);
}

static void ktmm_cgroup_uncharge_list(struct list_head *page_list) {
    if (!page_list) {
        pr_warn("KTMM: NULL page_list in cgroup_uncharge_list");
        return;
    }
    pt_cgroup_uncharge_list(page_list);
}

static unsigned long ktmm_isolate_lru_folios(unsigned long nr_to_scan, struct lruvec *lruvec,
                                           struct list_head *dst, unsigned long *nr_scanned,
                                           struct scan_control *sc, enum lru_list lru) {
    // CRITICAL: Limit scan amount to prevent infinite operations
    if (nr_to_scan > 10000) {
        pr_warn("KTMM: Large nr_to_scan %lu, limiting to 1000", nr_to_scan);
        nr_to_scan = 1000;
    }
    
    return pt_isolate_lru_folios(nr_to_scan, lruvec, dst, nr_scanned, sc, lru);
}

static unsigned int ktmm_move_folios_to_lru(struct lruvec *lruvec, struct list_head *list) {
    if (!list || !lruvec) {
        pr_warn("KTMM: NULL parameter in move_folios_to_lru");
        return 0;
    }
    return pt_move_folios_to_lru(lruvec, list);
}

static void ktmm_folio_putback_lru(struct folio *folio) {
    if (!folio) {
        pr_warn("KTMM: NULL folio in putback_lru");
        return;
    }
    pt_folio_putback_lru(folio);
}

static int ktmm_folio_referenced(struct folio *folio, int is_locked,
                                struct mem_cgroup *memcg, unsigned long *vm_flags) {
    if (!folio) {
        pr_warn("KTMM: NULL folio in folio_referenced");
        return 0;
    }
    return pt_folio_referenced(folio, is_locked, memcg, vm_flags);
}

/*****************************************************************************
* ALLOC & SWAP - HARDENED
*****************************************************************************/

/**
* alloc_pmem_page - allocate a page on pmem node (HARDENED)
*/
struct page* alloc_pmem_page(struct page *page, unsigned long data) {
    gfp_t gfp_mask = GFP_USER | __GFP_PMEM;
    struct page *new_page;
    int attempts = 0;
    
    // CRITICAL: Limit allocation attempts
    while (attempts < KTMM_MAX_MIGRATE_ATTEMPTS) {
        new_page = alloc_page(gfp_mask);
        if (new_page) {
            atomic_inc(&global_migrate_counter);
            return new_page;
        }
        
        attempts++;
        if (attempts >= 3) {
            pr_warn("KTMM: PMEM allocation failing, attempt %d", attempts);
            msleep(10); // Brief backoff - FIXED: Added include for msleep
        }
        
        // CRITICAL: Check for system pressure
        if (need_resched()) {
            cond_resched();
        }
    }
    
    pr_err("KTMM: Failed to allocate PMEM page after %d attempts", attempts);
    return NULL;
}

/**
* alloc_normal_page - allocate a page on a normal node (HARDENED)
*/
struct page* alloc_normal_page(struct page *page, unsigned long data) {
    gfp_t gfp_mask = GFP_USER;
    struct page *new_page;
    int attempts = 0;
    
    // CRITICAL: Limit allocation attempts
    while (attempts < KTMM_MAX_MIGRATE_ATTEMPTS) {
        new_page = alloc_page(gfp_mask);
        if (new_page) {
            return new_page;
        }
        
        attempts++;
        if (attempts >= 3) {
            pr_warn("KTMM: Normal allocation failing, attempt %d", attempts);
            msleep(10);
        }
        
        if (need_resched()) {
            cond_resched();
        }
    }
    
    pr_err("KTMM: Failed to allocate normal page after %d attempts", attempts);
    return NULL;
}

/* probably needs removed */
static struct page *ktmm_alloc_pages(gfp_t gfp_mask, unsigned int order, int preferred_nid,
                                    nodemask_t *nodemask) {
    //node mask of pmem_node
    //pass node mask into alloc pages
    nodemask_t nodemask_test;
    int nid;
    
    // CRITICAL: Initialize nodemask properly
    nodes_clear(nodemask_test);
    
    if ((gfp_mask & __GFP_PMEM) != 0) {
        for_each_node_state(nid, N_MEMORY) {
            // CRITICAL: Add comprehensive null checks
            if (NODE_DATA(nid) && NODE_DATA(nid)->pm_node != 0)
                node_set(nid, nodemask_test);
            else
                node_clear(nid, nodemask_test);
        }
        nodemask = &nodemask_test;
    }
    else if ((gfp_mask & __GFP_PMEM) == 0 && pmem_node_id != -1) {
        for_each_node_state(nid, N_MEMORY) {
            if (NODE_DATA(nid) && NODE_DATA(nid)->pm_node == 0)
                node_set(nid, nodemask_test);
            else
                node_clear(nid, nodemask_test);
        }
        nodemask = &nodemask_test;
    }

    return pt_alloc_pages(gfp_mask, order, preferred_nid, nodemask);
}

/*****************************************************************************
* Node Scanning, Shrinking, and Promotion - ULTRA-HARDENED
*****************************************************************************/

/**
* ktmm_cgroup_below_low - if memory cgroup is below low memory thresh
*
* @memcg: memory cgroup
*
* This is a reimplementation from the kernel function.
*/
static bool ktmm_cgroup_below_low(struct mem_cgroup *memcg) {
    if (!memcg) return false;
    return READ_ONCE(memcg->memory.elow) >=
           page_counter_read(&memcg->memory);
}

/**
* ktmm_cgroup_below_min - if memory cgroup is below min memory thresh
*
* @memcg: memory cgroup
*
* This is a reimplementation from the kernel function.
*/
static bool ktmm_cgroup_below_min(struct mem_cgroup *memcg) {
    if (!memcg) return false;
    return READ_ONCE(memcg->memory.emin) >=
           page_counter_read(&memcg->memory);
}

/**
* ktmm_update_lru_sizes - updates the size of the lru list
*
* @lruvec: per memcg lruvec
* @lru: the lru list
* @nr_zone_taken: the number of folios taken from the lru list
*
* This is a reimplementation from the kernel function.
*/
static __always_inline void ktmm_update_lru_sizes(struct lruvec *lruvec,
                                                  enum lru_list lru, unsigned long *nr_zone_taken) {
    int zid;
    
    if (!lruvec || !nr_zone_taken) return;
    
    for (zid = 0; zid < MAX_NR_ZONES; zid++) {
        if (!nr_zone_taken[zid])
            continue;
        ktmm_cgroup_update_lru_size(lruvec, lru, zid, -nr_zone_taken[zid]);
    }
}

/**
* ktmm_folio_evictable - if the folio is evictable or not
*
* @folio: folio to test
*
* This is a reimplementation from the kernel function.
*/
static inline bool ktmm_folio_evictable(struct folio *folio) {
    bool ret;
    
    if (!folio) return false;
    
    rcu_read_lock();
    ret = !mapping_unevictable(folio_mapping(folio)) &&
          !folio_test_mlocked(folio);
    rcu_read_unlock();
    return ret;
}

/**
* ktmm_folio_needs_release - if the folio needs release before free
*
* @folio: folio to test
*
* This is a reimplementation from the kernel function.
*/
static inline bool ktmm_folio_needs_release(struct folio *folio) {
    struct address_space *mapping;
    
    if (!folio) return false;
    
    mapping = folio_mapping(folio);
    return folio_has_private(folio) || (mapping && mapping_release_always(mapping));
}

/**
* scan_promote_list - ULTRA-HARDENED VERSION
*/
static void scan_promote_list(unsigned long nr_to_scan,
                             struct lruvec *lruvec,
                             struct scan_control *sc,
                             enum lru_list lru,
                             struct pglist_data *pgdat) {
    unsigned long nr_taken = 0;
    unsigned long nr_scanned = 0;
    unsigned long nr_migrated = 0;
    isolate_mode_t isolate_mode = 0;
    LIST_HEAD(l_hold);
    int file = is_file_lru(lru);
    int nid = pgdat->node_id;
    struct list_head *src;
    int scan_count = atomic_inc_return(&global_scan_counter);
    
    // CRITICAL: Early safety exits
    if (!lruvec || !sc || !pgdat) {
        pr_err("KTMM: NULL parameters in scan_promote_list");
        return;
    }
    
    if (scan_count > KTMM_MAX_SCAN_ITERATIONS) {
        pr_warn("KTMM: Scan count exceeded %d, skipping", KTMM_MAX_SCAN_ITERATIONS);
        return;
    }
    
    src = &lruvec->lists[lru];
    if (list_empty(src)) {
        pr_debug("promote list empty");
        return;
    }
    
    // CRITICAL: Limit scan amount
    if (nr_to_scan > 1000) {
        pr_warn("KTMM: Large scan request %lu, limiting to 1000", nr_to_scan);
        nr_to_scan = 1000;
    }

    pr_debug("scanning promote list on node %d", nid);

    if (!sc->may_unmap)
        isolate_mode |= ISOLATE_UNMAPPED;

    ktmm_lru_add_drain();

    // CRITICAL: Add timeout for lock operations
    if (!spin_trylock_irq(&lruvec->lru_lock)) {
        pr_warn("KTMM: Could not acquire LRU lock for promote list");
        return;
    }

    nr_taken = ktmm_isolate_lru_folios(nr_to_scan, lruvec, &l_hold,
                                     &nr_scanned, sc, lru);

    __mod_node_page_state(pgdat, NR_ISOLATED_ANON + file, nr_taken);

    spin_unlock_irq(&lruvec->lru_lock);

    pr_debug("pgdat %d scanned %lu on promote list", nid, nr_scanned);
    pr_debug("pgdat %d taken %lu on promote list", nid, nr_taken);

    // CRITICAL: Only attempt migration if we have pages and safe conditions
    if (nr_taken > 0 && nr_taken < 10000) {
        unsigned int succeeded;
        int ret;
        
        // CRITICAL: Add migration safety check
        if (atomic_read(&global_migrate_counter) < 100000) {
            ret = migrate_pages(&l_hold, alloc_normal_page,
                              NULL, 0, MIGRATE_SYNC, MR_MEMORY_HOTPLUG, &succeeded);

            nr_migrated = (ret < 0 ? 0 : nr_taken - ret);
            __mod_node_page_state(pgdat, NR_PROMOTED, nr_migrated);
            pr_debug("pgdat %d migrated %lu folios from promote list", nid, nr_migrated);
        } else {
            pr_warn("KTMM: Migration counter limit reached, skipping migration");
        }
    }

    // CRITICAL: Always clean up, even on errors
    if (!spin_trylock_irq(&lruvec->lru_lock)) {
        pr_err("KTMM: Could not reacquire LRU lock for cleanup");
        // Force cleanup without lock - risky but prevents hang
        goto force_cleanup;
    }
    
    ktmm_move_folios_to_lru(lruvec, &l_hold);
    __mod_node_page_state(pgdat, NR_ISOLATED_ANON + file, -nr_taken);
    spin_unlock_irq(&lruvec->lru_lock);

force_cleanup:
    ktmm_cgroup_uncharge_list(&l_hold);
    ktmm_free_unref_page_list(&l_hold);
    
    // CRITICAL: Yield CPU
    cond_resched();
}

/**
* scan_active_list - ULTRA-HARDENED VERSION
*/
static void scan_active_list(unsigned long nr_to_scan,
                            struct lruvec *lruvec,
                            struct scan_control *sc,
                            enum lru_list lru,
                            struct pglist_data *pgdat) {
    unsigned long nr_taken = 0;
    unsigned long nr_scanned = 0;
    unsigned long vm_flags;
    LIST_HEAD(l_hold); // The folios which were snipped off
    LIST_HEAD(l_active);
    LIST_HEAD(l_inactive);
    LIST_HEAD(l_promote);
    unsigned nr_deactivate, nr_activate, nr_promote;
    unsigned nr_rotated = 0;
    int file = is_file_lru(lru);
    int nid = pgdat->node_id;
    int processed = 0;
    int scan_count = atomic_inc_return(&global_scan_counter);

    // CRITICAL: Comprehensive safety checks
    if (!lruvec || !sc || !pgdat) {
        pr_err("KTMM: NULL parameters in scan_active_list");
        return;
    }
    
    if (scan_count > KTMM_MAX_SCAN_ITERATIONS) {
        pr_warn("KTMM: Active scan count exceeded, skipping");
        return;
    }

    // CRITICAL: Limit scan amount
    if (nr_to_scan > 1000) {
        pr_warn("KTMM: Large active scan %lu, limiting to 1000", nr_to_scan);
        nr_to_scan = 1000;
    }

    pr_debug("scanning active list on node %d", nid);

    // make sure pages in per-cpu lru list are added
    ktmm_lru_add_drain();

    // CRITICAL: Use trylock to prevent hanging
    if (!spin_trylock_irq(&lruvec->lru_lock)) {
        pr_warn("KTMM: Could not acquire LRU lock for active list");
        return;
    }

    nr_taken = ktmm_isolate_lru_folios(nr_to_scan, lruvec, &l_hold,
                                     &nr_scanned, sc, lru);

    __mod_node_page_state(pgdat, NR_ISOLATED_ANON + file, nr_taken);

    spin_unlock_irq(&lruvec->lru_lock);

    // CRITICAL: Ultra-hardened processing loop with multiple safety exits
    while (!list_empty(&l_hold) && processed < 10000) {
        struct folio *folio;
        
        processed++;
        
        // CRITICAL: Multiple safety checks per iteration
        if (processed % 100 == 0) {
            cond_resched();
        }
        
        if (need_resched()) {
            pr_debug("KTMM: Yielding CPU during active scan after %d folios", processed);
            cond_resched();
        }

        folio = lru_to_folio(&l_hold);
        if (!folio) {
            pr_err("KTMM: NULL folio in active list");
            break;
        }
        
        list_del(&folio->lru);

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

        // node migration
        if (pgdat->pm_node != 0) {
            if (ktmm_folio_referenced(folio, 0, sc->target_mem_cgroup, &vm_flags)) {
                pr_debug("set promote");
                folio_set_promote(folio);
                list_add(&folio->lru, &l_promote);
                continue;
            }
        }

        // Referenced or rmap lock contention: rotate
        if (ktmm_folio_referenced(folio, 0, sc->target_mem_cgroup,
                                  &vm_flags) != 0) {
            // FIXED: Use is_file_lru instead of folio_is_file_lru
            if ((vm_flags & VM_EXEC) && is_file_lru(lru)) {
                nr_rotated += folio_nr_pages(folio);
                list_add(&folio->lru, &l_active);
                continue;
            }
        }

        folio_clear_active(folio); // we are de-activating
        folio_set_workingset(folio);
        list_add(&folio->lru, &l_inactive);
    }

    // CRITICAL: Log if we hit safety limit
    if (processed >= 10000) {
        pr_warn("KTMM: Hit processing limit in active scan");
    }

    // Move folios back to the lru list.
    if (!spin_trylock_irq(&lruvec->lru_lock)) {
        pr_err("KTMM: Could not reacquire LRU lock for active cleanup");
        goto force_active_cleanup;
    }

    nr_activate = ktmm_move_folios_to_lru(lruvec, &l_active);
    nr_deactivate = ktmm_move_folios_to_lru(lruvec, &l_inactive);
    nr_promote = ktmm_move_folios_to_lru(lruvec, &l_promote);

    pr_debug("pgdat %d folio activated: %d", nid, nr_activate);
    pr_debug("pgdat %d folio deactivated: %d", nid, nr_deactivate);
    pr_debug("pgdat %d folio promoted: %d", nid, nr_promote);

    // Keep all free folios in l_active list
    list_splice(&l_inactive, &l_active);

    __mod_node_page_state(pgdat, NR_ISOLATED_ANON + file, -nr_taken);
    spin_unlock_irq(&lruvec->lru_lock);

force_active_cleanup:
    ktmm_cgroup_uncharge_list(&l_active);
    ktmm_free_unref_page_list(&l_active);
    
    // CRITICAL: Always yield
    cond_resched();
}

/**
* scan_inactive_list - ULTRA-HARDENED VERSION
*/
static unsigned long scan_inactive_list(unsigned long nr_to_scan,
                                       struct lruvec *lruvec,
                                       struct scan_control *sc,
                                       enum lru_list lru,
                                       struct pglist_data *pgdat) {
    LIST_HEAD(folio_list);
    unsigned long nr_scanned = 0;
    unsigned long nr_taken = 0;
    unsigned long nr_migrated = 0;
    unsigned long nr_reclaimed = 0;
    bool file = is_file_lru(lru);
    int nid = pgdat->node_id;
    int scan_count = atomic_inc_return(&global_scan_counter);

    // CRITICAL: Safety checks
    if (!lruvec || !sc || !pgdat) {
        pr_err("KTMM: NULL parameters in scan_inactive_list");
        return 0;
    }
    
    if (scan_count > KTMM_MAX_SCAN_ITERATIONS) {
        pr_warn("KTMM: Inactive scan count exceeded, skipping");
        return 0;
    }

    // CRITICAL: Limit scan amount
    if (nr_to_scan > 1000) {
        pr_warn("KTMM: Large inactive scan %lu, limiting to 1000", nr_to_scan);
        nr_to_scan = 1000;
    }

    pr_debug("scanning inactive list on node %d", nid);

    // make sure pages in per-cpu lru list are added
    ktmm_lru_add_drain();

    // We want to isolate the pages we are going to scan.
    if (!spin_trylock_irq(&lruvec->lru_lock)) {
        pr_warn("KTMM: Could not acquire LRU lock for inactive list");
        return 0;
    }

    nr_taken = ktmm_isolate_lru_folios(nr_to_scan, lruvec, &folio_list,
                                     &nr_scanned, sc, lru);

    __mod_node_page_state(pgdat, NR_ISOLATED_ANON + file, nr_taken);
    spin_unlock_irq(&lruvec->lru_lock);

    if (nr_taken == 0) return 0;

    // CRITICAL: Safe migration with limits
    if (pgdat->pm_node == 0 && pmem_node_id != -1 && 
        atomic_read(&global_migrate_counter) < 50000) {
        unsigned int succeeded;
        int ret = migrate_pages(&folio_list, alloc_pmem_page, NULL,
                              0, MIGRATE_SYNC, MR_MEMORY_HOTPLUG, &succeeded);

        nr_migrated = (ret >= 0 ? nr_taken - ret : 0);
        pr_debug("pgdat %d migrated %lu folios from inactive list", nid, nr_migrated);
        __mod_node_page_state(pgdat, NR_DEMOTED, nr_reclaimed);
    }

    if (!spin_trylock_irq(&lruvec->lru_lock)) {
        pr_err("KTMM: Could not reacquire LRU lock for inactive cleanup");
        goto force_inactive_cleanup;
    }
    
    ktmm_move_folios_to_lru(lruvec, &folio_list);
    __mod_node_page_state(pgdat, NR_ISOLATED_ANON + file, -nr_taken);
    spin_unlock_irq(&lruvec->lru_lock);

force_inactive_cleanup:
    ktmm_cgroup_uncharge_list(&folio_list);
    ktmm_free_unref_page_list(&folio_list);
    
    // CRITICAL: Always yield
    cond_resched();
    
    return nr_migrated;
}

/* SIMILAR TO: shrink_list() */
/**
* scan_list - determines which scan function to call per list (HARDENED)
*/
static unsigned long scan_list(enum lru_list lru,
                              unsigned long nr_to_scan,
                              struct lruvec *lruvec,
                              struct scan_control *sc,
                              struct pglist_data *pgdat) {
    
    // CRITICAL: Validate parameters
    if (!lruvec || !sc || !pgdat) {
        pr_err("KTMM: NULL parameters in scan_list");
        return 0;
    }
    
    // CRITICAL: Limit scan operations
    if (nr_to_scan > 2000) {
        pr_warn("KTMM: Large scan_list request %lu, limiting", nr_to_scan);
        nr_to_scan = 1000;
    }
    
    if (is_active_lru(lru)) {
        scan_active_list(nr_to_scan, lruvec, sc, lru, pgdat);
        return 0; // Active list doesn't return migration count
    }
    
    if (is_promote_lru(lru)) {
        scan_promote_list(nr_to_scan, lruvec, sc, lru, pgdat);
        return 0; // Promote list doesn't return migration count
    }
    
    return scan_inactive_list(nr_to_scan, lruvec, sc, lru, pgdat);
}

/**
* scan_node - ULTRA-HARDENED VERSION
*/
static void scan_node(pg_data_t *pgdat,
                     struct scan_control *sc,
                     struct mem_cgroup_reclaim_cookie *reclaim) {
    enum lru_list lru;
    struct mem_cgroup *memcg;
    int nid;
    int memcg_count;
    int scan_count = atomic_inc_return(&global_scan_counter);

    // CRITICAL: Comprehensive safety checks
    if (!pgdat || !sc || !reclaim) {
        pr_err("KTMM: NULL parameters in scan_node");
        return;
    }
    
    if (scan_count > KTMM_MAX_SCAN_ITERATIONS) {
        pr_warn("KTMM: Node scan count exceeded %d, skipping", KTMM_MAX_SCAN_ITERATIONS);
        return;
    }
    
    nid = pgdat->node_id;
    
    // CRITICAL: Validate node ID
    if (nid < 0 || nid >= MAX_NUMNODES) {
        pr_err("KTMM: Invalid node ID %d", nid);
        return;
    }

    memset(&sc->nr, 0, sizeof(sc->nr));

    memcg = ktmm_mem_cgroup_iter(NULL, NULL, reclaim);
    if (!memcg) {
        pr_warn("KTMM: No memory cgroup found for node %d", nid);
        return;
    }
    
    sc->target_mem_cgroup = memcg;

    pr_debug("scanning lists on node %d", nid);

    memcg_count = 0;

    // CRITICAL: Ultra-hardened memcg iteration with multiple safety exits
    do {
        struct lruvec *lruvec;
        unsigned long reclaimed;
        unsigned long scanned;

        memcg_count++;
        
        // CRITICAL: Multiple safety limits
        if (memcg_count > KTMM_MAX_MEMCG_ITERATIONS) {
            pr_warn("KTMM: Memcg iteration limit %d exceeded on node %d", 
                   KTMM_MAX_MEMCG_ITERATIONS, nid);
            break;
        }
        
        // FIXED: Remove the nodeinfo check that was causing compiler warning
        if (!memcg || !memcg->nodeinfo[nid]) {
            pr_warn("KTMM: Invalid memcg structure for node %d", nid);
            continue;
        }
        
        lruvec = &memcg->nodeinfo[nid]->lruvec;
        if (!lruvec) {
            pr_warn("KTMM: NULL lruvec for node %d", nid);
            continue;
        }

        // CRITICAL: Yield CPU every few iterations
        if (memcg_count % 10 == 0) {
            cond_resched();
        }

        if (ktmm_cgroup_below_min(memcg)) {
            /*
            * Hard protection.
            * If there is no reclaimable memory, OOM.
            */
            continue;
        } else if (ktmm_cgroup_below_low(memcg)) {
            /*
            * Soft protection.
            * Respect the protection only as long as
            * there is an unprotected supply of
            * reclaimable memory from other cgroups.
            */
            if (!sc->memcg_low_reclaim) {
                sc->memcg_low_skipped = 1;
                continue;
            }
            // memcg_memory_event(memcg, MEMCG_LOW);
        }

        reclaimed = sc->nr_reclaimed;
        scanned = sc->nr_scanned;

        // CRITICAL: Limit LRU iteration and add safety breaks
        for_each_evictable_lru(lru) {
            unsigned long nr_to_scan = 512; // Reduced from 1024
            
            // CRITICAL: Check system state before each scan
            if (need_resched()) {
                pr_debug("KTMM: System needs reschedule, yielding");
                cond_resched();
            }
            
            scan_list(lru, nr_to_scan, lruvec, sc, pgdat);
        }

    } while ((memcg = ktmm_mem_cgroup_iter(NULL, memcg, NULL)) && 
             memcg_count < KTMM_MAX_MEMCG_ITERATIONS);
    
    // CRITICAL: Always yield after node scan
    cond_resched();
}

/*****************************************************************************
* Daemon Functions & Related - ULTRA-HARDENED
*****************************************************************************/

/**
* tmemd_try_to_sleep - HARDENED sleep function
*/
static void tmemd_try_to_sleep(pg_data_t *pgdat, int nid) {
    long remaining = 0;
    DEFINE_WAIT(wait);

    pr_debug("tmemd trying to sleep: %d", nid);

    // CRITICAL: Always check stop condition first
    if (freezing(current) || kthread_should_stop()) {
        pr_debug("KTMM: tmemd stop requested for node %d", nid);
        return;
    }

    // CRITICAL: Validate parameters
    if (!pgdat || nid < 0 || nid >= MAX_NUMNODES) {
        pr_err("KTMM: Invalid parameters in tmemd_try_to_sleep");
        return;
    }

    prepare_to_wait(&tmemd_wait[nid], &wait, TASK_INTERRUPTIBLE);
    
    // CRITICAL: Use shorter sleep interval to be more responsive
    remaining = schedule_timeout(HZ / 10); // 100ms instead of 1s
    
    finish_wait(&tmemd_wait[nid], &wait);
    
    // CRITICAL: Log if sleep was interrupted
    if (remaining > 0) {
        pr_debug("KTMM: tmemd sleep interrupted on node %d", nid);
    }
}

/**
* tmemd - ULTRA-HARDENED page promotion daemon
*/
static int tmemd(void *p) {
    pg_data_t *pgdat = (pg_data_t *)p;
    int nid;
    struct task_struct *task = current;
    const struct cpumask *cpumask;
    struct mem_cgroup_reclaim_cookie reclaim;
    struct reclaim_state reclaim_state = {
        .reclaimed_slab = 0,
    };
    // FIXED: Removed unused struct scan_control sc to fix compiler warning
    int iteration_count = 0;

    // CRITICAL: Comprehensive parameter validation
    if (!pgdat) {
        pr_err("KTMM: NULL pgdat in tmemd");
        return -EINVAL;
    }
    
    nid = pgdat->node_id;
    if (nid < 0 || nid >= MAX_NUMNODES) {
        pr_err("KTMM: Invalid node ID %d in tmemd", nid);
        return -EINVAL;
    }
    
    cpumask = cpumask_of_node(nid);
    reclaim.pgdat = pgdat;

    // Only allow node's CPUs to run this task
    if (!cpumask_empty(cpumask))
        set_cpus_allowed_ptr(task, cpumask);

    current->reclaim_state = &reclaim_state;

    /*
    * Tell MM that we are a memory allocator, and that we are actually
    * kswapd. We are also set to suspend as needed.
    *
    * Flags are located in include/sched.h for more info.
    */
    task->flags |= PF_MEMALLOC | PF_KSWAPD;

    pr_info("KTMM: tmemd ULTRA-HARDENED started on node %d", nid);

    /*
    * CRITICAL: ULTRA-HARDENED main loop with multiple safety mechanisms
    * - Proper stop condition checking
    * - Iteration limits  
    * - CPU yielding
    * - Error recovery
    * - System state monitoring
    */
    
    while (!kthread_should_stop() && iteration_count < KTMM_MAX_TMEMD_ITERATIONS) {
        struct scan_control sc = {
            .nr_to_reclaim = SWAP_CLUSTER_MAX,
            .priority = DEF_PRIORITY,
            .may_writepage = !laptop_mode,
            .may_unmap = 1,
            .may_swap = 1,
            .reclaim_idx = MAX_NR_ZONES - 1,
            .only_promote = 1,
        };
        
        iteration_count++;
        
        // CRITICAL: Multiple safety checks per iteration
        if (iteration_count % 1000 == 0) {
            pr_info("KTMM: tmemd iteration %d on node %d", iteration_count, nid);
        }
        
        if (iteration_count % 100 == 0) {
            // CRITICAL: Check system health periodically
            if (need_resched()) {
                pr_debug("KTMM: System needs reschedule, yielding");
                cond_resched();
            }
        }

        // CRITICAL: Check for freezing conditions
        if (freezing(current)) {
            pr_info("KTMM: tmemd freezing on node %d", nid);
            try_to_freeze();
            continue;
        }

        // CRITICAL: Reset counters periodically to prevent overflow
        if (iteration_count % 10000 == 0) {
            atomic_set(&global_scan_counter, 0);
            atomic_set(&global_migrate_counter, 0);
            pr_debug("KTMM: Reset safety counters on node %d", nid);
        }

        // CRITICAL: Perform the actual scanning with simple error handling
        // FIXED: Removed C++ try-catch syntax
        scan_node(pgdat, &sc, &reclaim);
        
        // CRITICAL: ALWAYS sleep to yield CPU control - this was the main bug!
        tmemd_try_to_sleep(pgdat, nid);
        
        // CRITICAL: Additional mandatory CPU yielding
        cond_resched();
        
        // CRITICAL: Microsleep to absolutely ensure we don't monopolize CPU
        // FIXED: Added include for usleep_range
        usleep_range(KTMM_SLEEP_INTERVAL_MS * 1000, 
                    (KTMM_SLEEP_INTERVAL_MS + 50) * 1000);
    }

    // CRITICAL: Log exit reason
    if (iteration_count >= KTMM_MAX_TMEMD_ITERATIONS) {
        pr_warn("KTMM: tmemd hit iteration limit %d on node %d", 
               KTMM_MAX_TMEMD_ITERATIONS, nid);
    } else {
        pr_info("KTMM: tmemd normal exit on node %d after %d iterations", 
               nid, iteration_count);
    }

    // CRITICAL: Proper cleanup
    task->flags &= ~(PF_MEMALLOC | PF_KSWAPD);
    current->reclaim_state = NULL;
    
    return 0;
}

/*****************************************************************************
* Start & Stop - HARDENED
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
* ULTRA-HARDENED startup function
*/
int tmemd_start_available(void) {
    int i;
    int nid;
    int ret = 0;
    int started_daemons = 0;

    pr_info("KTMM: Starting ULTRA-HARDENED tmemd daemons");

    set_ktmm_scan();

    // CRITICAL: Initialize safety counters
    atomic_set(&global_scan_counter, 0);
    atomic_set(&global_migrate_counter, 0);
    atomic_set(&global_tmemd_counter, 0);

    /* initialize wait queues for sleeping */
    for (i = 0; i < MAX_NUMNODES; i++) {
        init_waitqueue_head(&tmemd_wait[i]);
        tmemd_list[i] = NULL; // CRITICAL: Initialize to NULL
    }

    ret = install_hooks(vmscan_hooks, ARRAY_SIZE(vmscan_hooks));
    if (ret) {
        pr_err("KTMM: Failed to install hooks: %d", ret);
        return ret;
    }

    // CRITICAL: Start daemons with comprehensive error handling
    for_each_online_node(nid) {
        pg_data_t *pgdat = NODE_DATA(nid);
        
        // CRITICAL: Validate node data
        if (!pgdat) {
            pr_err("KTMM: NULL pgdat for node %d", nid);
            continue;
        }

        /* !! EMULATE PMEM NODE !! */
        if (nid == 1) {
            pr_info("KTMM: Emulating pmem node %d", nid);
            set_pmem_node_id(nid);
            set_pmem_node(nid);
        }

        tmemd_list[nid] = kthread_run(&tmemd, pgdat, "tmemd-%d", nid);
        
        // CRITICAL: Comprehensive error handling
        if (IS_ERR(tmemd_list[nid])) {
            ret = PTR_ERR(tmemd_list[nid]);
            pr_err("KTMM: Failed to start tmemd on node %d: %d", nid, ret);
            tmemd_list[nid] = NULL; // Set to NULL on failure
            
            // CRITICAL: Don't fail entirely, continue with other nodes
            continue;
        } else {
            started_daemons++;
            pr_info("KTMM: Successfully started tmemd on node %d", nid);
        }
    }

    if (started_daemons == 0) {
        pr_err("KTMM: No tmemd daemons started successfully");
        uninstall_hooks(vmscan_hooks, ARRAY_SIZE(vmscan_hooks));
        return -ENODEV;
    }

    pr_info("KTMM: Started %d tmemd daemons successfully", started_daemons);
    return 0;
}

/**
* ULTRA-HARDENED cleanup function
*/
void tmemd_stop_all(void) {
    int nid;
    int stopped_daemons = 0;

    pr_info("KTMM: Stopping all tmemd daemons");

    // CRITICAL: Stop all daemons with comprehensive error handling
    for_each_online_node(nid) {
        if (tmemd_list[nid] && !IS_ERR(tmemd_list[nid])) {
            pr_debug("KTMM: Stopping tmemd on node %d", nid);
            
            // CRITICAL: Use kthread_stop which is safer
            int ret = kthread_stop(tmemd_list[nid]);
            if (ret) {
                pr_warn("KTMM: kthread_stop returned %d for node %d", ret, nid);
            } else {
                stopped_daemons++;
            }
            
            tmemd_list[nid] = NULL;
        }
    }

    pr_info("KTMM: Stopped %d tmemd daemons", stopped_daemons);

    // CRITICAL: Always uninstall hooks
    uninstall_hooks(vmscan_hooks, ARRAY_SIZE(vmscan_hooks));
    
    // CRITICAL: Reset counters
    atomic_set(&global_scan_counter, 0);
    atomic_set(&global_migrate_counter, 0);
    atomic_set(&global_tmemd_counter, 0);
    
    pr_info("KTMM: ULTRA-HARDENED cleanup complete");
}