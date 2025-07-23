#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <assert.h>
// LF input/output ports
typedef struct port_t {
    bool is_present;
    int32_t value;
} port_t;

void lf_set(port_t *p, int32_t v) {
    p->is_present = true;
    p->value = v;
}


// modifies
// inputs
port_t *trigger;
// outputs
port_t *left;
port_t *right;


// nondet functions for replacing undefined functions
int32_t nondet_int32_t();

void encoders_reaction_1() {
    // Also, the sign is reversed, where reverse increases, so we negate.
    /* int32_t rcount = -quadrature_encoder_get_count(pio0, RIGHT_SM); */
    /* int32_t lcount = -quadrature_encoder_get_count(pio0, LEFT_SM); */
    // TODO: add info about pio0
    int32_t rcount = nondet_int32_t();
    int32_t lcount = nondet_int32_t();
    lf_set(right, rcount);
    lf_set(left, lcount);
}

// nondet functions
port_t nondet_port_t();

int main() {
    // malloc inputs and modifies
    trigger = calloc(1, sizeof(port_t));
    __CPROVER_assume(trigger);
    // malloc outputs and modifies
    left = calloc(1, sizeof(port_t));
    right = calloc(1, sizeof(port_t));
    __CPROVER_assume(left && right);
    // initialize inputs and modifies with nondet values
    *trigger = nondet_port_t();
    // set modifies to be init values

    __CPROVER_assume(PRECONDITION);
    encoders_reaction_1();
    assert(POSTCONDITION);
}
