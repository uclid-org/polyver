#include <stdlib.h>
#include <stdbool.h>
#include <math.h>
#include <assert.h>
// LF input/output ports
typedef struct port_t {
    bool is_present;
    int value;
} port_t;

void lf_set(port_t *p, int v) {
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
port_t *tilt_roll;
// outputs
port_t *m_left_power;
port_t *m_right_power;

void hillclimb_climbing_reaction_1() {
    int roll = tilt_roll->value;
    if ((roll > 0 && self->uphill) || (roll < 0 && !self->uphill)) {
        lf_set(m_left_power, 1);
        lf_set(m_right_power, 0);
    }
    else {
        lf_set(m_left_power, 0);
        lf_set(m_right_power, 1);
    }
}

// nondet functions
hillclimb_self_t nondet_hillclimb_self_t();
port_t nondet_port_t();

int main() {
    // malloc inputs and modifies
    init_self = calloc(1, sizeof(hillclimb_self_t));
    tilt_roll = calloc(1, sizeof(port_t));
    __CPROVER_assume(init_self && tilt_roll);
    // malloc outputs and modifies
    self = calloc(1, sizeof(hillclimb_self_t));
    m_left_power = calloc(1, sizeof(port_t));
    m_right_power = calloc(1, sizeof(port_t));
    __CPROVER_assume(self && m_left_power && m_right_power);
    // initialize inputs and modifies with nondet values
    *init_self = nondet_hillclimb_self_t();
    *tilt_roll = nondet_port_t();
    // set modifies to be init values
    self->uphill = init_self->uphill;

    __CPROVER_assume(PRECONDITION);
    hillclimb_climbing_reaction_1();
    assert(POSTCONDITION);
}
