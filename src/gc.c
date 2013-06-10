/*
** gc.c - garbage collector for mruby
**
** See Copyright Notice in mruby.h
*/

#ifndef SIZE_MAX
 /* Some versions of VC++
  * has SIZE_MAX in stdint.h
  */
# include <limits.h>
#endif
#include <windows.h>
#include <string.h>
#include "mruby.h"
#include "mruby/array.h"
#include "mruby/class.h"
#include "mruby/data.h"
#include "mruby/hash.h"
#include "mruby/proc.h"
#include "mruby/range.h"
#include "mruby/string.h"
#include "mruby/variable.h"
#include "mruby/gc.h"


struct free_obj {
  MRB_OBJECT_HEADER;
  struct RBasic *next;
};

typedef struct {
  union {
    struct free_obj free;
    struct RBasic basic;
    struct RObject object;
    struct RClass klass;
    struct RString string;
    struct RArray array;
    struct RHash hash;
    struct RRange range;
    struct RData data;
    struct RProc proc;
  } as;
} RVALUE;

//#define GC_PROFILE 1
//#define GC_DEBUG 1

#ifdef GC_PROFILE
#include <stdio.h>
#include <sys/time.h>

static double program_invoke_time = 0;
static double gc_time = 0;
static double gc_total_time = 0;

static double
gettimeofday_time(void)
{
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return tv.tv_sec + tv.tv_usec * 1e-6;
}

#define GC_INVOKE_TIME_REPORT(with) do {\
  fprintf(stderr, "%s\n", with);\
  fprintf(stderr, "gc_invoke: %19.3f\n", gettimeofday_time() - program_invoke_time);\
} while(0)

#define GC_TIME_START do {\
  gc_time = gettimeofday_time();\
} while(0)

#define GC_TIME_STOP_AND_REPORT do {\
  gc_time = gettimeofday_time() - gc_time;\
  gc_total_time += gc_time;\
  fprintf(stderr, "gc_state: %d\n", mrb->gc_state);\
  fprintf(stderr, "live: %d\n", mrb->live);\
  fprintf(stderr, "gc_time: %30.20f\n", gc_time);\
  fprintf(stderr, "gc_total_time: %30.20f\n\n", gc_total_time);\
} while(0)
#else
#define GC_INVOKE_TIME_REPORT(s)
#define GC_TIME_START
#define GC_TIME_STOP_AND_REPORT
#endif

#ifdef GC_DEBUG
#include <assert.h>
#define gc_assert(expect) assert(expect)
#define DEBUG(x) (x)
#else
#define gc_assert(expect) ((void)0)
#define DEBUG(x)
#endif

#define GC_STEP_SIZE 1024

void*
mrb_realloc(mrb_state *mrb, void *p, size_t len)
{
  void *p2;

  p2 = (mrb->allocf)(mrb, p, len, mrb->ud);

  if (!p2 && len > 0 && mrb->heaps) {
    mrb_garbage_collect(mrb);
    p2 = (mrb->allocf)(mrb, p, len, mrb->ud);
  }

  if (!p2 && len) {
    if (mrb->out_of_memory) {
      /* mrb_panic(mrb); */
    }
    else {
      mrb->out_of_memory = 1;
      mrb_raise(mrb, E_RUNTIME_ERROR, "Out of memory");
    }
  }
  else {
    mrb->out_of_memory = 0;
  }

  return p2;
}

void*
mrb_malloc(mrb_state *mrb, size_t len)
{
  return mrb_realloc(mrb, 0, len);
}

void*
mrb_calloc(mrb_state *mrb, size_t nelem, size_t len)
{
  void *p = NULL;
  size_t size;

  if (nelem <= SIZE_MAX / len) {
    size = nelem * len;
    p = mrb_realloc(mrb, 0, size);

    if (p && size > 0)
      memset(p, 0, size);
  }

  return p;
}

void
mrb_free(mrb_state *mrb, void *p)
{
  (mrb->allocf)(mrb, p, 0, mrb->ud);
}

#ifndef MRB_HEAP_PAGE_SIZE
#define MRB_HEAP_PAGE_SIZE 1024
#endif

struct heap_page {
  struct RBasic *freelist;
  struct heap_page *prev;
  struct heap_page *next;
  struct heap_page *free_next;
  struct heap_page *free_prev;
  mrb_bool old:1;
  RVALUE objects[MRB_HEAP_PAGE_SIZE];
};

static void
link_heap_page(mrb_state *mrb, struct heap_page *page)
{
  page->next = mrb->heaps;
  if (mrb->heaps)
    mrb->heaps->prev = page;
  mrb->heaps = page;
}

static void
unlink_heap_page(mrb_state *mrb, struct heap_page *page)
{
  if (page->prev)
    page->prev->next = page->next;
  if (page->next)
    page->next->prev = page->prev;
  if (mrb->heaps == page)
    mrb->heaps = page->next;
  page->prev = NULL;
  page->next = NULL;
}

static void
link_free_heap_page(mrb_state *mrb, struct heap_page *page)
{
  page->free_next = mrb->free_heaps;
  if (mrb->free_heaps) {
    mrb->free_heaps->free_prev = page;
  }
  mrb->free_heaps = page;
}

static void
unlink_free_heap_page(mrb_state *mrb, struct heap_page *page)
{
  if (page->free_prev)
    page->free_prev->free_next = page->free_next;
  if (page->free_next)
    page->free_next->free_prev = page->free_prev;
  if (mrb->free_heaps == page)
    mrb->free_heaps = page->free_next;
  page->free_prev = NULL;
  page->free_next = NULL;
}

static void
add_heap(mrb_state *mrb)
{
  struct heap_page *page = (struct heap_page *)mrb_calloc(mrb, 1, sizeof(struct heap_page));
  RVALUE *p, *e;
  struct RBasic *prev = NULL;

  for (p = page->objects, e=p+MRB_HEAP_PAGE_SIZE; p<e; p++) {
    p->as.free.tt = MRB_TT_FREE;
    p->as.free.next = prev;
    prev = &p->as.basic;
  }
  page->freelist = prev;

  link_heap_page(mrb, page);
  link_free_heap_page(mrb, page);
}

void
mrb_init_heap(mrb_state *mrb)
{
  mrb->heaps = 0;
  mrb->free_heaps = 0;
  add_heap(mrb);

#ifdef GC_PROFILE
  program_invoke_time = gettimeofday_time();
#endif
}

static void obj_free(mrb_state *mrb, struct RBasic *obj);

void
mrb_free_heap(mrb_state *mrb)
{
  struct heap_page *page = mrb->heaps;
  struct heap_page *tmp;
  RVALUE *p, *e;

  while (page) {
    tmp = page;
    page = page->next;
    for (p = tmp->objects, e=p+MRB_HEAP_PAGE_SIZE; p<e; p++) {
      if (p->as.free.tt != MRB_TT_FREE)
        obj_free(mrb, &p->as.basic);
    }
    mrb_free(mrb, tmp);
  }
}

static void
gc_protect(mrb_state *mrb, struct RBasic *p)
{
  if (mrb->arena_idx >= MRB_ARENA_SIZE) {
    /* arena overflow error */
    mrb->arena_idx = MRB_ARENA_SIZE - 4; /* force room in arena */
    mrb_raise(mrb, E_RUNTIME_ERROR, "arena overflow error");
  }
  mrb->arena[mrb->arena_idx++] = p;
}

void
mrb_gc_protect(mrb_state *mrb, mrb_value obj)
{
  if (mrb_special_const_p(obj)) return;
  gc_protect(mrb, mrb_basic_ptr(obj));
}

struct RBasic*
mrb_obj_alloc(mrb_state *mrb, enum mrb_vtype ttype, struct RClass *cls)
{
  struct RBasic *p;
  static const RVALUE RVALUE_zero = { { { MRB_TT_FALSE } } };

//#ifdef MRB_GC_STRESS
//  mrb_garbage_collect(mrb);
//#endif
  if (mrb->free_heaps == NULL) {
      mrb_garbage_collect(mrb);
      add_heap(mrb);
  }

  p = mrb->free_heaps->freelist;
  mrb->free_heaps->freelist = ((struct free_obj*)p)->next;
  if (mrb->free_heaps->freelist == NULL) {
    unlink_free_heap_page(mrb, mrb->free_heaps);
  }

  mrb->live++;
  gc_protect(mrb, p);
  *(RVALUE *)p = RVALUE_zero;
  p->tt = ttype;
  p->c = cls;
  paint_white(p);
  return p;
}

static void
mark_context(mrb_state *mrb, struct mrb_context *c)
{
  size_t i;
  size_t e;
  mrb_callinfo *ci;

  /* mark stack */
  e = c->stack - c->stbase;
  if (c->ci) e += c->ci->nregs;
  if (c->stbase + e > c->stend) e = c->stend - c->stbase;
  for (i=0; i<e; i++) {
    mrb_gc_mark_value(mrb, c->stbase[i]);
  }
  /* mark ensure stack */
  e = (c->ci) ? c->ci->eidx : 0;
  for (i=0; i<e; i++) {
    mrb_gc_mark(mrb, (struct RBasic*)c->ensure[i]);
  }
  /* mark closure */
  for (ci = c->cibase; ci <= c->ci; ci++) {
    if (!ci) continue;
    mrb_gc_mark(mrb, (struct RBasic*)ci->env);
    mrb_gc_mark(mrb, (struct RBasic*)ci->proc);
    mrb_gc_mark(mrb, (struct RBasic*)ci->target_class);
  }
  if (c->prev && c->prev->fib) {
    mrb_gc_mark(mrb, (struct RBasic*)c->prev->fib);
  }
}

void
mrb_gc_mark(mrb_state *mrb, struct RBasic *obj)
{
  if (obj == 0) return;
  if (!is_white(obj)) return;

  paint_black(obj);
  mrb_gc_mark(mrb, (struct RBasic*)obj->c);
  switch (obj->tt) {
  case MRB_TT_ICLASS:
    mrb_gc_mark(mrb, (struct RBasic*)((struct RClass*)obj)->super);
    break;

  case MRB_TT_CLASS:
  case MRB_TT_MODULE:
  case MRB_TT_SCLASS:
    {
      struct RClass *c = (struct RClass*)obj;

      mrb_gc_mark_mt(mrb, c);
      mrb_gc_mark(mrb, (struct RBasic*)c->super);
    }
    /* fall through */

  case MRB_TT_OBJECT:
  case MRB_TT_DATA:
    mrb_gc_mark_iv(mrb, (struct RObject*)obj);
    break;

  case MRB_TT_PROC:
    {
      struct RProc *p = (struct RProc*)obj;

      mrb_gc_mark(mrb, (struct RBasic*)p->env);
      mrb_gc_mark(mrb, (struct RBasic*)p->target_class);
    }
    break;

  case MRB_TT_ENV:
    {
      struct REnv *e = (struct REnv*)obj;

      if (e->cioff < 0) {
        int i, len;

        len = (int)e->flags;
        for (i=0; i<len; i++) {
          mrb_gc_mark_value(mrb, e->stack[i]);
        }
      }
    }
    break;

  case MRB_TT_FIBER:
    {
      struct mrb_context *c = ((struct RFiber*)obj)->cxt;

      mark_context(mrb, c);
    }
    break;

  case MRB_TT_ARRAY:
    {
      struct RArray *a = (struct RArray*)obj;
      size_t i, e;

      for (i=0,e=a->len; i<e; i++) {
        mrb_gc_mark_value(mrb, a->ptr[i]);
      }
    }
    break;

  case MRB_TT_HASH:
    mrb_gc_mark_iv(mrb, (struct RObject*)obj);
    mrb_gc_mark_hash(mrb, (struct RHash*)obj);
    break;

  case MRB_TT_STRING:
    break;

  case MRB_TT_RANGE:
    {
      struct RRange *r = (struct RRange*)obj;

      if (r->edges) {
        mrb_gc_mark_value(mrb, r->edges->beg);
        mrb_gc_mark_value(mrb, r->edges->end);
      }
    }
    break;

  default:
    break;
  }
}



static void
obj_free(mrb_state *mrb, struct RBasic *obj)
{
//  DEBUG(printf("obj_free(%p,tt=%d)\n",obj,obj->tt));
  switch (obj->tt) {
    /* immediate - no mark */
  case MRB_TT_TRUE:
  case MRB_TT_FIXNUM:
  case MRB_TT_SYMBOL:
    /* cannot happen */
    return;

  case MRB_TT_FLOAT:
#ifdef MRB_WORD_BOXING
    break;
#else
    return;
#endif

  case MRB_TT_OBJECT:
    mrb_gc_free_iv(mrb, (struct RObject*)obj);
    break;

  case MRB_TT_CLASS:
  case MRB_TT_MODULE:
  case MRB_TT_SCLASS:
    mrb_gc_free_mt(mrb, (struct RClass*)obj);
    mrb_gc_free_iv(mrb, (struct RObject*)obj);
    break;

  case MRB_TT_ENV:
    {
      struct REnv *e = (struct REnv*)obj;

      if (e->cioff < 0) {
        mrb_free(mrb, e->stack);
        e->stack = 0;
      }
    }
    break;

  case MRB_TT_FIBER:
    {
      struct mrb_context *c = ((struct RFiber*)obj)->cxt;

      mrb_free_context(mrb, c);
    }
    break;

  case MRB_TT_ARRAY:
    if (obj->flags & MRB_ARY_SHARED)
      mrb_ary_decref(mrb, ((struct RArray*)obj)->aux.shared);
    else
      mrb_free(mrb, ((struct RArray*)obj)->ptr);
    break;

  case MRB_TT_HASH:
    mrb_gc_free_iv(mrb, (struct RObject*)obj);
    mrb_gc_free_hash(mrb, (struct RHash*)obj);
    break;

  case MRB_TT_STRING:
    mrb_gc_free_str(mrb, (struct RString*)obj);
    break;

  case MRB_TT_RANGE:
    mrb_free(mrb, ((struct RRange*)obj)->edges);
    break;

  case MRB_TT_DATA:
    {
      struct RData *d = (struct RData*)obj;
      if (d->type->dfree) {
        d->type->dfree(mrb, d->data);
      }
      mrb_gc_free_iv(mrb, (struct RObject*)obj);
    }
    break;

  default:
    break;
  }
  obj->tt = MRB_TT_FREE;
}

static void
mark(mrb_state *mrb)
//static DWORD WINAPI mark( LPVOID lpParameter )
{
  int j;
  size_t i, e;
//  mrb_state *mrb = (mrb_state *)lpParameter;

  mrb_gc_mark_gv(mrb);
  /* mark arena */
  for (i=0,e=mrb->arena_idx; i<e; i++) {
    mrb_gc_mark(mrb, mrb->arena[i]);
  }
  /* mark class hierarchy */
  mrb_gc_mark(mrb, (struct RBasic*)mrb->object_class);
  /* mark top_self */
  mrb_gc_mark(mrb, (struct RBasic*)mrb->top_self);
  /* mark exception */
  mrb_gc_mark(mrb, (struct RBasic*)mrb->exc);

  mark_context(mrb, mrb->root_c);
  /* mark irep pool */
  if (mrb->irep) {
    size_t len = mrb->irep_len;
    if (len > mrb->irep_capa) len = mrb->irep_capa;
    for (i=0; i<len; i++) {
      mrb_irep *irep = mrb->irep[i];
      if (!irep) continue;
      for (j=0; j<irep->plen; j++) {
        mrb_gc_mark_value(mrb, irep->pool[j]);
      }
    }
  }
//  ExitThread( 0 );
}

static void
prepare_sweep(mrb_state *mrb)
{
  mrb->gc_state = GC_STATE_SWEEP;
  mrb->sweeps = mrb->heaps;
  mrb->gc_live_after_mark = mrb->live;
}

static size_t
sweep(mrb_state *mrb)
{
  struct heap_page *page = mrb->sweeps;

  while (page) {
    RVALUE *p = page->objects;
    RVALUE *e = p + MRB_HEAP_PAGE_SIZE;
    size_t freed = 0;
    int dead_slot = 1;
    int full = (page->freelist == NULL);

    while (p<e) {
      if (is_white(&p->as.basic) || is_dead(mrb, &p->as.basic)) {
        if (p->as.basic.tt != MRB_TT_FREE) {
          obj_free(mrb, &p->as.basic);
          p->as.free.next = page->freelist;
          page->freelist = (struct RBasic*)p;
          freed++;
        }
      }
      else {
        paint_white(&p->as.basic);
        dead_slot = 0;
      }
      p++;
    }

    /* free dead slot */
    if (dead_slot && freed < MRB_HEAP_PAGE_SIZE) {
      struct heap_page *next = page->next;

      unlink_heap_page(mrb, page);
      unlink_free_heap_page(mrb, page);
      mrb_free(mrb, page);
      page = next;
    }
    else {
      if (full && freed > 0) {
        link_free_heap_page(mrb, page);
      }
      page = page->next;
    }
    mrb->live -= freed;
    mrb->gc_live_after_mark -= freed;
  }
  mrb->sweeps = page;
  return 0;
}

static size_t
gc(mrb_state *mrb)
{
//    HANDLE hThread[4];
//    mrb->gc_state = GC_STATE_MARK;

//    hThread[0] = CreateThread(NULL, 0, &mark, mrb, 0, 0);
//    hThread[1] = CreateThread(NULL, 0, &mark2, mrb, 0, 0);
//    hThread[2] = CreateThread(NULL, 0, &mark, mrb, 0, 0);
//    hThread[3] = CreateThread(NULL, 0, &mark, mrb, 0, 0);
//    WaitForSingleObject(hThread[0], INFINITE);
//    WaitForMultipleObjects(2, hThread, TRUE, INFINITE);
//    CloseHandle(hThread[0]);
//    CloseHandle(hThread[1]);
//    CloseHandle(hThread[2]);
//    CloseHandle(hThread[3]);
    mark(mrb);
    mrb->gc_state = GC_STATE_SWEEP;
    prepare_sweep(mrb);
    sweep(mrb);
    mrb->gc_state = GC_STATE_NONE;
    return 0;
}

void
mrb_garbage_collect(mrb_state *mrb)
{
  if (mrb->gc_disabled) return;
//  GC_INVOKE_TIME_REPORT("mrb_garbage_collect()");
//  GC_TIME_START;

  gc(mrb);

//  GC_TIME_STOP_AND_REPORT;
}

int
mrb_gc_arena_save(mrb_state *mrb)
{
  return mrb->arena_idx;
}

void
mrb_gc_arena_restore(mrb_state *mrb, int idx)
{
  mrb->arena_idx = idx;
}

/*
 * Field write barrier
 *   Paint obj(Black) -> value(White) to obj(Black) -> value(Gray).
 */

void
mrb_field_write_barrier(mrb_state *mrb, struct RBasic *obj, struct RBasic *value)
{
  return;
}

/*
 * Write barrier
 *   Paint obj(Black) to obj(Gray).
 *
 *   The object that is painted gray will be traversed atomically in final
 *   mark phase. So you use this write barrier if it's frequency written spot.
 *   e.g. Set element on Array.
 */

void
mrb_write_barrier(mrb_state *mrb, struct RBasic *obj)
{
  return;
}

/*
 *  call-seq:
 *     GC.start                     -> nil
 *
 *  Initiates full garbage collection.
 *
 */

static mrb_value
gc_start(mrb_state *mrb, mrb_value obj)
{
  mrb_garbage_collect(mrb);
  return mrb_nil_value();
}

/*
 *  call-seq:
 *     GC.enable    -> true or false
 *
 *  Enables garbage collection, returning <code>true</code> if garbage
 *  collection was previously disabled.
 *
 *     GC.disable   #=> false
 *     GC.enable    #=> true
 *     GC.enable    #=> false
 *
 */

static mrb_value
gc_enable(mrb_state *mrb, mrb_value obj)
{
  int old = mrb->gc_disabled;

  mrb->gc_disabled = FALSE;

  return mrb_bool_value(old);
}

/*
 *  call-seq:
 *     GC.disable    -> true or false
 *
 *  Disables garbage collection, returning <code>true</code> if garbage
 *  collection was already disabled.
 *
 *     GC.disable   #=> false
 *     GC.disable   #=> true
 *
 */

static mrb_value
gc_disable(mrb_state *mrb, mrb_value obj)
{
  int old = mrb->gc_disabled;

  mrb->gc_disabled = TRUE;

  return mrb_bool_value(old);
}

void
mrb_objspace_each_objects(mrb_state *mrb, each_object_callback* callback, void *data)
{
    struct heap_page* page = mrb->heaps;

    while (page != NULL) {
        RVALUE *p, *pend;

        p = page->objects;
        pend = p + MRB_HEAP_PAGE_SIZE;
        for (;p < pend; p++) {
           (*callback)(mrb, &p->as.basic, data);
        }

        page = page->next;
    }
}

static mrb_value
gc_dummy_set(mrb_state *mrb, mrb_value obj)
{
  return mrb_bool_value(1);
}

static mrb_value
gc_dummy_get(mrb_state *mrb, mrb_value obj)
{
  return mrb_bool_value(1);
}

void
mrb_init_gc(mrb_state *mrb)
{
  struct RClass *gc;

  gc = mrb_define_module(mrb, "GC");

  mrb_define_class_method(mrb, gc, "start", gc_start, MRB_ARGS_NONE());
  mrb_define_class_method(mrb, gc, "enable", gc_enable, MRB_ARGS_NONE());
  mrb_define_class_method(mrb, gc, "disable", gc_disable, MRB_ARGS_NONE());
  mrb_define_class_method(mrb, gc, "interval_ratio", gc_dummy_get, MRB_ARGS_NONE());
  mrb_define_class_method(mrb, gc, "interval_ratio=", gc_dummy_set, MRB_ARGS_REQ(1));
  mrb_define_class_method(mrb, gc, "step_ratio", gc_dummy_get, MRB_ARGS_NONE());
  mrb_define_class_method(mrb, gc, "step_ratio=", gc_dummy_set, MRB_ARGS_REQ(1));
  mrb_define_class_method(mrb, gc, "generational_mode=", gc_dummy_get, MRB_ARGS_REQ(1));
  mrb_define_class_method(mrb, gc, "generational_mode", gc_dummy_set, MRB_ARGS_NONE());
}

