#![deny(warnings)]

use std::{env, error::Error};

fn main() -> Result<(), Box<dyn Error>> {
    let target = env::var("TARGET")?;

    if target.starts_with("thumbv6m-") {
        println!("cargo:rustc-cfg=armv6m");
    } else if target.starts_with("thumbv7m-") {
        println!("cargo:rustc-cfg=armv7m");
    } else if target.starts_with("thumbv7em-") {
        println!("cargo:rustc-cfg=armv7m");
    } else if target.starts_with("armv7r-") | target.starts_with("armebv7r-") {
        println!("cargo:rustc-cfg=armv7r");
    } else if target.starts_with("thumbv8m.base") {
        println!("cargo:rustc-cfg=armv8m_base");
    } else if target.starts_with("thumbv8m.main") {
        println!("cargo:rustc-cfg=armv8m_main");
    } else if target.starts_with("armv7-") | target.starts_with("armv7a-") {
        println!("cargo:rustc-cfg=armv7a");
    }

    // built-in targets with no atomic / CAS support as of nightly-2022-01-13
    // AND not supported by the atomic-polyfill crate
    // see the `no-atomics.sh` / `no-cas.sh` script sitting next to this file
    match &target[..] {
        "avr-unknown-gnu-atmega328"
        | "bpfeb-unknown-none"
        | "bpfel-unknown-none"
        | "msp430-none-elf"
        // | "riscv32i-unknown-none-elf"    // supported by atomic-polyfill
        // | "riscv32imc-unknown-none-elf"  // supported by atomic-polyfill
        | "thumbv4t-none-eabi"
        // | "thumbv6m-none-eabi"           // supported by atomic-polyfill
         => {}

        _ => {
            println!("cargo:rustc-cfg=has_cas");
        }
    };

    match &target[..] {
        "avr-unknown-gnu-atmega328"
        | "msp430-none-elf"
        | "avr-atmega328p"
        | "avr-atmega2560"
        // | "riscv32i-unknown-none-elf"    // supported by atomic-polyfill
        // | "riscv32imc-unknown-none-elf"  // supported by atomic-polyfill
        => {}

        _ => {
            println!("cargo:rustc-cfg=has_atomics");
        }
    };

    // Let the code know if it should use atomic-polyfill or not, and what aspects
    // of polyfill it requires
    match &target[..] {
        "riscv32i-unknown-none-elf"
        | "riscv32imc-unknown-none-elf"
        | "avr-atmega328p"
        | "avr-atmega2560" => {
            println!("cargo:rustc-cfg=full_atomic_polyfill");
            println!("cargo:rustc-cfg=cas_atomic_polyfill");
        }

        "thumbv6m-none-eabi" => {
            println!("cargo:rustc-cfg=cas_atomic_polyfill");
        }
        _ => {}
    }

    Ok(())
}
