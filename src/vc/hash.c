#include <stddef.h>

extern void * malloc (size_t n);
extern void exit(int n);
extern size_t strlen(const char *str);
extern char *strcpy(char *dest, const char *src);
extern int strcmp(const char *str1, const char *str2);

unsigned int hash (char *s) {
  unsigned int n=0;
  unsigned int i=0;
  int c=s[i];
  while (c) {
    n = n*65599u+(unsigned)c;
    i++;
    c=s[i];
  }
  return n;
}

struct cell {
  char *key;
  unsigned int count;
  struct cell *next;
};

enum {N = 109};

struct hashtable {
  struct cell *buckets[N];
};

char *copy_string (char *s) {
  int i,n = strlen(s)+1;
  char *p = malloc(n);
  if (!p) exit(1);
  strcpy(p,s);
  return p;
}

struct hashtable *new_table (void) {
  int i;
  struct hashtable *p = (struct hashtable *)malloc(sizeof(struct hashtable));
  if (!p) exit(1);
  for (i=0; i<N; i++) p->buckets[i]=NULL;
  return p;
}  

struct cell *new_cell (char *key, int count, struct cell *next) {
  struct cell *p = (struct cell *)malloc(sizeof(struct cell));
  if (!p) exit(1);
  p->key = copy_string(key);
  p->count = count;
  p->next = next;
  return p;
}

unsigned int get (struct hashtable *table, char *s) {
  unsigned int h = hash(s);
  unsigned int b = h % N;
  struct cell *p = table->buckets[b];
  while (p) {
    if (strcmp(p->key, s)==0)
      return p->count;
    p=p->next;
  }
  return 0;
}

void incr_list (struct cell **r0, char *s) {
  struct cell *p, **r;
  for(r=r0; ; r=&p->next) {
    p = *r;
    if (!p) {
      *r = new_cell(s,1,NULL);
      return;
    }
    if (strcmp(p->key, s)==0) {
      p->count++;
      return;
    }
  }
}  

void incr (struct hashtable *table, char *s) {
  unsigned int h = hash(s);
  unsigned int b = h % N;
  incr_list (& table->buckets[b], s);
}

void incrx (struct hashtable *table, char *s) {
  unsigned int h = hash(s);
  unsigned int b = h % N;
  struct cell *p = table->buckets[b];
  while (p) {
    if (strcmp(p->key, s)==0) {
      p->count++;
      return;
    }
    p=p->next;
  }
  table->buckets[b]=new_cell(s, 1, table->buckets[b]);
}


  
