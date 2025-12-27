#include <stdio.h>
#include <stdlib.h>

int main() {
  int* p1 = malloc(sizeof(int));
  *p1 = 123;

  int* p2 = p1;

  free(p1);

  printf("%d\n", *p2);

  free(p2);

  return 0;
}
