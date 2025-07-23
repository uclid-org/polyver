#include <stdint.h>
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

typedef struct bool_port_t {
    bool is_present;
    bool value;
} bool_port_t;


// modifies
// inputs
bool_port_t *trigger;
// outputs
port_t *x;
port_t *y;
port_t *z;

// imu.h
typedef struct _imu_inst {
    uint32_t set_baud;
    bool status;
} imu_inst_t;

typedef struct _axes_data {
    int x;
    int y;
    int z;
} axes_data_t;

// nondet functions to replace undefined functions
imu_inst_t nondet_imu_inst_t();
axes_data_t nondet_axes_data_t();

void accelerometer_reaction_1() {
    axes_data_t acc_data;
    /* imu_read_acc(&imu_instance, &acc_data); */
    // FIXME: imu_instance is not declared in the function
    imu_inst_t imu_instance = nondet_imu_inst_t();
    acc_data = nondet_axes_data_t();
    lf_set(x, acc_data.x);
    lf_set(y, acc_data.y);
    lf_set(z, acc_data.z);
}

// nondet functions
bool_port_t nondet_bool_port_t();

int main() {
    // malloc inputs and modifies
    trigger = calloc(1, sizeof(bool_port_t));
    __CPROVER_assume(trigger);
    // malloc outputs and modifies
    x = calloc(1, sizeof(port_t));
    y = calloc(1, sizeof(port_t));
    z = calloc(1, sizeof(port_t));
    __CPROVER_assume(x && y && z);
    // initialize inputs and modifies with nondet values
    *trigger = nondet_bool_port_t();
    // set modifies to be init values

    __CPROVER_assume(PRECONDITION);
    accelerometer_reaction_1();
    assert(POSTCONDITION);
}
