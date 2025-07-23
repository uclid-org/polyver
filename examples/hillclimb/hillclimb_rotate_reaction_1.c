#include <stdlib.h>
#include <stdbool.h>
#include <math.h>
#include <assert.h>
// mode enum
int STRAIGHT;
int init_mode;
int mode;

void lf_set_mode(int m) {
    mode = m;
}

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
port_t *g_z;
// outputs
port_t *m_left_power;
port_t *m_right_power;

void hillclimb_rotate_reaction_1() {
    if (fabs(g_z->value - self->last_angle) >= 180) {
        lf_set_mode(STRAIGHT);
        lf_set(m_left_power, 1);
        lf_set(m_right_power, 1);
        self->uphill = !self->uphill;
    }
}

// nondet functions
hillclimb_self_t nondet_hillclimb_self_t();
port_t nondet_port_t();
int nondet_int();

int main() {
    // malloc inputs and modifies
    init_self = calloc(1, sizeof(hillclimb_self_t));
    g_z = calloc(1, sizeof(port_t));
    __CPROVER_assume(init_self && g_z);
    // malloc outputs and modifies
    self = calloc(1, sizeof(hillclimb_self_t));
    m_left_power = calloc(1, sizeof(port_t));
    m_right_power = calloc(1, sizeof(port_t));
    __CPROVER_assume(self && m_left_power && m_right_power);
    // initialize inputs and modifies with nondet values
    *init_self = nondet_hillclimb_self_t();
    *g_z = nondet_port_t();
    init_mode = nondet_int();
    // set modifies to be init values
    self->uphill = init_self->uphill;
    self->last_angle = init_self->last_angle;
    mode = init_mode;

    __CPROVER_assume(PRECONDITION);
    hillclimb_rotate_reaction_1();
    assert(POSTCONDITION);
}
