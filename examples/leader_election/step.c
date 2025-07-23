#include <stdbool.h>

typedef struct node_t {
  int id;
  int m;
  int win;
} node_t;

node_t step(node_t src, node_t dst) {
    node_t ret;
    ret = dst;
    if (src.m == dst.id) {
        ret.win = 1;
    }
    if (src.m > dst.id) {
        ret.m = src.m;
    }
    return ret;
}

node_t nondet_node_t();

void main() {
    node_t src, dst, ret;
    src = nondet_node_t();
    dst = nondet_node_t();
    __CPROVER_assume(PRECONDITION);
    ret = step(src, dst);
    assert(POSTCONDITION);
}
