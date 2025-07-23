#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

int foo(unsigned int i)
{
    /* int ret = 0; */
    /* if (i > 0) */
    /*     ret = (i - 2 * (int)(rand() % 10)) & 1; */
    /* else */
    /*     ret = (i * i) % 2; */
    /* return i + ret * 20; */
    return i + 50;
}

int nondet_int();

int main() {
  int i = nondet_int();
  __CPROVER_assume(PRECONDITION);
  int r = foo(i);
  assert(POSTCONDITION);
}
