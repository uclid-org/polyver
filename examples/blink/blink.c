/**
 * Copyright (c) 2020 Raspberry Pi (Trading) Ltd.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

/***** CBMC *****/
/**
 * The code snippets within the CBMC block are fetched from the Pico SDK
 * codebase to give the below code some semantics. Otherwise, CBMC
 * treats them as empty functions.
 *
 * If the project depends on a library, we assume that the header files
 * from the library are available to the CBMC user. For C functions that
 * are defined outside of the user project, they are conservatively
 * treated as nondeterministic functions.
 *
 * This calls into question how CBMC can be integrated into a real project
 * like one that uses the Raspberry Pi Pico SDK. The fact that CBMC does
 * not use a CMake build system for the project under analysis makes
 * real-world integration difficult.
 */

#include "stdbool.h"
#include "stdint.h"

// <pico_sdk>/common/pico_base_headers/include/pico/types.h
typedef unsigned int uint;

// #include "pico/stdlib.h"
enum pico_error_codes {
    PICO_OK = 0,                                ///< No error; the operation succeeded
    PICO_ERROR_NONE = 0,                        ///< No error; the operation succeeded
    PICO_ERROR_GENERIC = -1,                    ///< An unspecified error occurred
    PICO_ERROR_TIMEOUT = -2,                    ///< The function failed due to timeout
    PICO_ERROR_NO_DATA = -3,                    ///< Attempt for example to read from an empty buffer/FIFO
    PICO_ERROR_NOT_PERMITTED = -4,              ///< Permission violation e.g. write to read-only flash partition, or security violation
    PICO_ERROR_INVALID_ARG = -5,                ///< Argument is outside of range of supported values`
    PICO_ERROR_IO = -6,                         ///< An I/O error occurred
    PICO_ERROR_BADAUTH = -7,                    ///< The authorization failed due to bad credentials
    PICO_ERROR_CONNECT_FAILED = -8,             ///< The connection failed
    PICO_ERROR_INSUFFICIENT_RESOURCES = -9,     ///< Dynamic allocation of resources failed
    PICO_ERROR_INVALID_ADDRESS = -10,           ///< Address argument was out-of-bounds or was determined to be an address that the caller may not access
    PICO_ERROR_BAD_ALIGNMENT = -11,             ///< Address was mis-aligned (usually not on word boundary)
    PICO_ERROR_INVALID_STATE = -12,             ///< Something happened or failed to happen in the past, and consequently we (currently) can't service the request
    PICO_ERROR_BUFFER_TOO_SMALL = -13,          ///< A user-allocated buffer was too small to hold the result or working state of this function
    PICO_ERROR_PRECONDITION_NOT_MET = -14,      ///< The call failed because another function must be called first
    PICO_ERROR_MODIFIED_DATA = -15,             ///< Cached data was determined to be inconsistent with the actual version of the data
    PICO_ERROR_INVALID_DATA = -16,              ///< A data structure failed to validate
    PICO_ERROR_NOT_FOUND = -17,                 ///< Attempted to access something that does not exist; or, a search failed
    PICO_ERROR_UNSUPPORTED_MODIFICATION = -18,  ///< Write is impossible based on previous writes; e.g. attempted to clear an OTP bit
    PICO_ERROR_LOCK_REQUIRED = -19,             ///< A required lock is not owned
    PICO_ERROR_VERSION_MISMATCH = -20,          ///< A version mismatch occurred (e.g. trying to run PIO version 1 code on RP2040)
    PICO_ERROR_RESOURCE_IN_USE = -21            ///< The call could not proceed because requires resourcesw were unavailable
};
//------------- LED -------------//
#ifndef PICO_DEFAULT_LED_PIN
#define PICO_DEFAULT_LED_PIN 25
#endif

// <pico_sdk>/host/hardware_gpio/include/hardware/gpio.h
enum gpio_function {
    GPIO_FUNC_XIP = 0,
    GPIO_FUNC_SPI = 1,
    GPIO_FUNC_UART = 2,
    GPIO_FUNC_I2C = 3,
    GPIO_FUNC_PWM = 4,
    GPIO_FUNC_SIO = 5,
    GPIO_FUNC_PIO0 = 6,
    GPIO_FUNC_PIO1 = 7,
    GPIO_FUNC_GPCK = 8,
    GPIO_FUNC_USB = 9,
    GPIO_FUNC_NULL = 0xf,
};
#define GPIO_OUT 1
#define GPIO_IN 0
/*! \brief Set a single GPIO direction
 *  \ingroup hardware_gpio
 *
 * \param gpio GPIO number
 * \param out true for out, false for in
 */
static inline void gpio_set_dir(uint gpio, bool out) {
#if PICO_USE_GPIO_COPROCESSOR
    gpioc_bit_oe_put(gpio, out);
#elif PICO_RP2040 || NUM_BANK0_GPIOS <= 32
    uint32_t mask = 1ul << gpio;
    if (out)
        gpio_set_dir_out_masked(mask);
    else
        gpio_set_dir_in_masked(mask);
#else
    uint32_t mask = 1u << (gpio & 0x1fu);
    if (gpio < 32) {
        if (out) {
            sio_hw->gpio_oe_set = mask;
        } else {
            sio_hw->gpio_oe_clr = mask;
        }
    } else {
        if (out) {
            sio_hw->gpio_hi_oe_set = mask;
        } else {
            sio_hw->gpio_hi_oe_clr = mask;
        }
    }
#endif
}
/****************/

// Pico W devices use a GPIO on the WIFI chip for the LED,
// so when building for Pico W, CYW43_WL_GPIO_LED_PIN will be defined
#ifdef CYW43_WL_GPIO_LED_PIN
#include "pico/cyw43_arch.h"
#endif

#ifndef LED_DELAY_MS
#define LED_DELAY_MS 200
#endif

// Perform initialisation
int pico_led_init(void) {
#if defined(PICO_DEFAULT_LED_PIN)
    // A device like Pico that uses a GPIO for the LED will define PICO_DEFAULT_LED_PIN
    // so we can use normal GPIO functionality to turn the led on and off
    gpio_init(PICO_DEFAULT_LED_PIN);
    gpio_set_dir(PICO_DEFAULT_LED_PIN, GPIO_OUT);
    return PICO_OK;
#elif defined(CYW43_WL_GPIO_LED_PIN)
    // For Pico W devices we need to initialise the driver etc
    return cyw43_arch_init();
#endif
}

// Turn the led on or off
int pico_set_led(bool led_on) {
#if defined(PICO_DEFAULT_LED_PIN)
    // Just set the GPIO on or off
    gpio_put(PICO_DEFAULT_LED_PIN, led_on);
#elif defined(CYW43_WL_GPIO_LED_PIN)
    // Ask the wifi "driver" to set the GPIO on or off
    cyw43_arch_gpio_put(CYW43_WL_GPIO_LED_PIN, led_on);
#endif

    // Other application logic
    int led_state = 0;
    if (led_on) led_state = 1;
    else led_state = 0;
    return led_state;
}

int main() {
    int rc = pico_led_init();
    hard_assert(rc == PICO_OK);

    bool led_on = nondet_bool();
    int led_state;
    __CPROVER_assume(PRECONDITION);
    led_state = pico_set_led(led_on);
    assert(POSTCONDITION);
}
