#include <stdlib.h>
#include <stdbool.h>
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

// declaration for instant_t, SEC, and lf_time_logical
typedef int instant_t;

int SEC(int ns) {
    return ns * 1e-9;
}

int nondet_int();
int lf_time_logical() {
    // FIXME: should `now` always be larger than `self->prev_time`?
    // if so add assume statement
    /* int now = nondet_int(); */
    /* __CPROVER_assume(now >= self->prev_time); */
    return nondet_int();
}

typedef struct trapezoidalintegrator_self_t {
    int s;
    int prev_in;
    instant_t prev_time;
} trapezoidalintegrator_self_t;

// modifies
trapezoidalintegrator_self_t *self;
trapezoidalintegrator_self_t *init_self;
// inputs
port_t *inp;
// outputs
port_t *out;

void trapezoidalintegrator_reaction_1() {
    // FIXME: should `now` always be larger than `self->prev_time`?
    instant_t now = lf_time_logical();
    if (self->prev_time > SEC(0)) {
      int interval = ((now - self->prev_time) * 1e-9);
      self->s += (inp->value + self->prev_in) * interval / 2;
    }
    lf_set(out, self->s);
    self->prev_in = inp->value;
    self->prev_time = now;
}

// nondet functions
port_t nondet_port_t();
trapezoidalintegrator_self_t nondet_trapezoidalintegrator_self_t();

int main() {
    // malloc inputs and modifies
    inp = calloc(1, sizeof(port_t));
    init_self = calloc(1, sizeof(trapezoidalintegrator_self_t));
    __CPROVER_assume(inp && init_self);
    // malloc outputs and modifies
    out = calloc(1, sizeof(port_t));
    self = calloc(1, sizeof(trapezoidalintegrator_self_t));
    __CPROVER_assume(out && self);
    // initialize inputs and modifies with nondet values
    *inp = nondet_port_t();
    *self = nondet_trapezoidalintegrator_self_t();
    // set modifies to be init values
    *init_self = *self;

    __CPROVER_assume(PRECONDITION);
    trapezoidalintegrator_reaction_1();
    assert(POSTCONDITION);
}
