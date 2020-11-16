#include <stddef.h>

extern void * malloc (size_t n);
extern void free (void *p);
extern void exit(int n);

struct cons {
  int value;
  struct cons *next;
};

struct stack {
  struct cons *top;
};

/* Verification of the first 3 functions is in Verif_stack.v */

struct stack *newstack(void) {
  struct stack *p;
  p = (struct stack *) malloc (sizeof (struct stack));
  if (!p) exit(1);
  p->top = NULL;
  return p;
}

void push (struct stack *p, int i) {
  struct cons *q;
  q = (struct cons *) malloc (sizeof (struct cons));
  if (!q) exit(1);
  q->value = i;
  q->next = p->top;
  p->top = q;
}

int pop (struct stack *p) {
  struct cons *q;
  int i;
  q = p->top;
  p->top = q->next;
  i = q->value;
  free(q);
  return i;
}

/* Verification of the next 3 functions is in Verif_triang.v */

void push_increasing (struct stack *st, int n) {
  int i;
  i=0;
  while (i<n) {
     i++;
     push(st,i);
  }
}

int pop_and_add (struct stack *st, int n) {
  int i=0;
  int t, s=0;
  while (i<n) {
    t=pop(st);
    s += t;
    i++;
  }
  return s;
}

int main (void) {
  struct stack *st;
  int i,t,s;
  st = newstack();
  push_increasing(st, 10);
  s = pop_and_add(st, 10);
  return s;
}
    
