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

// modifies
// inputs
port_t *x;
port_t *y;
port_t *z;
// outputs
port_t *pitch;
port_t *roll;

// nondet functions to replace undefined functions
double nondet_double();
double atan(double x) {
    return nondet_double();
}
double acos(double x) {
    return nondet_double();
}

void tilt_reaction_1() {
    /* int pitch_value = atan(x->value / z->value) * 180 / M_PI; */
    /* int roll_value = acos(y->value / sqrt(pow(x->value, 2) + pow(y->value, 2) + pow(z->value, 2))) * 180 / M_PI - 90; */
    int pitch_value = nondet_int();
    int roll_value = nondet_int();

    lf_set(pitch, pitch_value);
    lf_set(roll, roll_value);

}

// nondet functions
port_t nondet_port_t();
int nondet_int();

int main() {
    // malloc inputs and modifies
    x = calloc(1, sizeof(port_t));
    y = calloc(1, sizeof(port_t));
    z = calloc(1, sizeof(port_t));
    __CPROVER_assume(x && y && z);
    // malloc outputs and modifies
    pitch = calloc(1, sizeof(port_t));
    roll = calloc(1, sizeof(port_t));
    __CPROVER_assume(pitch && roll);
    // initialize inputs and modifies with nondet values
    *x = nondet_port_t();
    *y = nondet_port_t();
    *z = nondet_port_t();
    // set modifies to be init values

    __CPROVER_assume(PRECONDITION);
    tilt_reaction_1();
    assert(POSTCONDITION);
}
