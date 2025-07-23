#include <stdint.h>
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
port_t *left_power;
// outputs

#define MAX_MOTOR_POWER 0x0FFF

uint16_t nondet_uint16_t();
bool nondet_bool();

void set_power(int power, bool forward, bool left) {
    power = fabsf(power);
    if (power > 10) power = 10;
    uint16_t duty_cycle = (uint16_t)(power * MAX_MOTOR_POWER);
    /* motors_set_power(duty_cycle, forward, left); */
    duty_cycle = nondet_uint16_t();
    forward = nondet_bool();
    left = nondet_bool();
}

void motors_reaction_1() {
    bool forward = (left_power->value >= 0);
    set_power(left_power->value, forward, true);
}

// nondet functions
port_t nondet_port_t();

int main() {
    // malloc inputs and modifies
    left_power = calloc(1, sizeof(port_t));
    __CPROVER_assume(left_power);
    // malloc outputs and modifies
    // initialize inputs and modifies with nondet values
    *left_power = nondet_port_t();
    // set modifies to be init values

    __CPROVER_assume(PRECONDITION);
    motors_reaction_1();
    assert(POSTCONDITION);
}
