#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>
/**
Each c file contains a single reaction that takes no arguments and returns void.
All inputs and outputs are passed as pointers and are declared as global variables.
*/

typedef struct traffic_light_self_t {
    int _mode;
    int count;
} traffic_light_self_t;

// The user needs to provide a JSON file telling the interface
// the names and types of the function inputs and outputs.
traffic_light_self_t *self;
traffic_light_self_t *init_self;

void traffic_light_reaction_1() {
    self->_mode = 0;
    self->count = 58;
}

// cbmc nondet functions
traffic_light_self_t nondet_traffic_light_self_t();

int main() {
    // malloc inputs/outputs
    init_self = calloc(1, sizeof(traffic_light_self_t));
    self = calloc(1, sizeof(traffic_light_self_t));
    __CPROVER_assume(init_self && self);
    // assign nondet values
    *init_self = nondet_traffic_light_self_t();
    *self = nondet_traffic_light_self_t();

    self->_mode = init_self->_mode;
    self->count = init_self->count;

    __CPROVER_assume(PRECONDITION);
    traffic_light_reaction_1();
    assert(POSTCONDITION);
}
