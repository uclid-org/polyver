#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>
// LF input/output ports
typedef struct port_t {
    int is_present;
    int value;
} port_t;

// Maps to LF logical actions
typedef struct trigger_t {
    int is_present;
} trigger_t;

void lf_set(port_t *p, int v) {
    p->is_present = 1;
    p->value = v;
}

void lf_schedule(trigger_t *t, int additional_delay) {
    if (additional_delay == 0)
        t->is_present = 1;
}

typedef struct traffic_light_self_t {
    int _mode;
    int count;
} traffic_light_self_t;

traffic_light_self_t *self;
traffic_light_self_t *init_self;
trigger_t *resetCount;
port_t *sigG;
port_t *sigY;
port_t *sigR;
port_t *pedestrian;

void traffic_light_reaction_2() {
    // RED
    if (self->_mode == 0) {
        if (self->count >= 60) {
            lf_set(sigG, 1);
            lf_schedule(resetCount, 0);
        } else {
            self->count += 1;
        }
    }
    // GREEN
    else if (self->_mode == 1) {
        if (pedestrian->is_present) {
            if (self->count >= 60) {
                lf_set(sigY, 1);
                lf_schedule(resetCount, 0);
            } else {
                self->count += 1;
            }
        } else {
            self->count += 1;
        }
    }
    // YELLOW
    else if (self->_mode == 2) {
        if (self->count >= 5) {
            lf_set(sigR, 1);
            lf_schedule(resetCount, 0);
        } else {
            self->count += 1;
        }
    }
    // PENDING
    else {
        if (self->count >= 60) {
            lf_set(sigY, 1);
            lf_schedule(resetCount, 0);
        } else {
            self->count += 1;
        }
    }
}

// nondet functions
traffic_light_self_t nondet_traffic_light_self_t();
port_t nondet_port_t();
trigger_t nondet_trigger_t();

int main() {
    // malloc inputs
    init_self = calloc(1, sizeof(traffic_light_self_t));
    pedestrian = calloc(1, sizeof(port_t));
    __CPROVER_assume(init_self && pedestrian);
    // malloc outputs
    self = calloc(1, sizeof(traffic_light_self_t));
    sigG = calloc(1, sizeof(port_t));
    sigY = calloc(1, sizeof(port_t));
    sigR = calloc(1, sizeof(port_t));
    resetCount = calloc(1, sizeof(trigger_t));
    __CPROVER_assume(self && sigG && sigY && sigR && resetCount);
    sigG->is_present = 0; sigY->is_present = 0; sigR->is_present = 0; resetCount->is_present = 0;
    sigG->value = 0; sigY->value = 0; sigR->value = 0;
    // initialize with nondet values
    *init_self = nondet_traffic_light_self_t();
    *pedestrian = nondet_port_t();

    self->_mode = init_self->_mode;
    self->count = init_self->count;

    __CPROVER_assume(PRECONDITION);
    traffic_light_reaction_2();
    assert(POSTCONDITION);
}
