#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>
// LF input/output ports
typedef struct bool_port_t {
    bool is_present;
    bool value;
} bool_port_t;

void lf_set(bool_port_t *p, bool v) {
    p->is_present = true;
    p->value = v;
}

typedef struct hillclimb_self_t {
    bool uphill;
    int last_angle;
} hillclimb_self_t;

// modifies
hillclimb_self_t *self;
hillclimb_self_t *init_self;
// inputs
// outputs
bool_port_t *a_trigger;
bool_port_t *g_trigger;


void hillclimb_reaction_2() {
    lf_set(a_trigger, true);
    lf_set(g_trigger, true);
}

// nondet functions
hillclimb_self_t nondet_hillclimb_self_t();
bool_port_t nondet_bool_port_t();

int main() {
    // malloc inputs and modifies
    init_self = calloc(1, sizeof(hillclimb_self_t));
    __CPROVER_assume(init_self);
    // malloc outputs and modifies
    self = calloc(1, sizeof(hillclimb_self_t));
    a_trigger = calloc(1, sizeof(bool_port_t));
    g_trigger = calloc(1, sizeof(bool_port_t));
    __CPROVER_assume(self && a_trigger && g_trigger);
    // initialize inputs and modifies with nondet values
    *init_self = nondet_hillclimb_self_t();
    // set modifies to be init values
    self->last_angle = init_self->last_angle;
    self->uphill = init_self->uphill;

    __CPROVER_assume(PRECONDITION);
    hillclimb_reaction_2();
    assert(POSTCONDITION);
}
