#include <stddef.h>

struct list {int head; struct list *tail;};

struct list *append (struct list *x, struct list *y) {
  struct list *t, *u;
  if (x==NULL)
    return y;
  else {
    t = x;
    u = t->tail;
    while (u!=NULL) {
      t = u;
      u = t->tail;
    }
    t->tail = y;
    return x;
  }
}

struct list * append2 (struct list * x, struct list * y) {
  struct list * * retp, * * curp;
  retp = & x;
  curp = & x;
  while ( * curp != NULL ) {
    curp = & (( * curp ) -> tail);
  }
  * curp = y;
  return * retp;
}
