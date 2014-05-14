// morepaths.c
// anomaly with missing paths when function ends with loop construct

struct Node {
  struct Node *next;
};

void append(struct Node *head, struct Node *toAdd)
{
  struct Node *p = head;

  while (p != (struct Node*)0) {
    thmprv_invariant(1);
    p = p;
  }

  //p = toAdd;
}
