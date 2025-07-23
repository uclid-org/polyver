#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>
/**
Each c file contains a single reaction that takes no arguments and returns void.
All inputs and outputs are passed as pointers and are declared as global variables.
*/

typedef struct port_t {
    int is_present;
    int value;
} port_t;

void lf_set(port_t *p, int v) {
    p->is_present = 1;
    p->value = v;
}

// The user needs to provide a JSON file telling the interface
// the names and types of the function inputs and outputs.
port_t *out;

void pedestrian_reaction_1() {
    lf_set(out, 1);
}

// nondet functions
port_t nondet_port_t();

int main() {
    // malloc inputs/outputs
    out = calloc(1, sizeof(port_t));
    __CPROVER_assume(out);
    *out = nondet_port_t();

    __CPROVER_assume(PRECONDITION);
    pedestrian_reaction_1();
    assert(POSTCONDITION);
}
