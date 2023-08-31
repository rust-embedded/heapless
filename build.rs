#![deny(warnings)]

use std::{
    env,
    error::Error,
    fs,
    path::Path,
    process::{Command, ExitStatus, Stdio},
};

use rustc_version::Channel;

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

    let is_avr = env::var("CARGO_CFG_TARGET_ARCH").as_deref() == Ok("avr");

    // built-in targets with no atomic / CAS support as of nightly-2022-01-13
    // AND not supported by the atomic-polyfill crate
    // see the `no-atomics.sh` / `no-cas.sh` script sitting next to this file
    if is_avr {
        // lacks cas
    } else {
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
        }
    };

    if is_avr {
        // lacks atomics
    } else {
        match &target[..] {
        "msp430-none-elf"
        // | "riscv32i-unknown-none-elf"    // supported by atomic-polyfill
        // | "riscv32imc-unknown-none-elf"  // supported by atomic-polyfill
        => {}

        _ => {
            println!("cargo:rustc-cfg=has_atomics");
        }
    }
    };

    // Let the code know if it should use atomic-polyfill or not, and what aspects
    // of polyfill it requires
    if is_avr {
        println!("cargo:rustc-cfg=full_atomic_polyfill");
        println!("cargo:rustc-cfg=cas_atomic_polyfill");
    } else {
        match &target[..] {
            "riscv32i-unknown-none-elf"
            | "riscv32imc-unknown-none-elf"
            | "xtensa-esp32s2-none-elf" => {
                println!("cargo:rustc-cfg=full_atomic_polyfill");
                println!("cargo:rustc-cfg=cas_atomic_polyfill");
            }

            "thumbv6m-none-eabi" => {
                println!("cargo:rustc-cfg=cas_atomic_polyfill");
            }
            _ => {}
        }
    }

    if !matches!(
        rustc_version::version_meta().unwrap().channel,
        Channel::Stable | Channel::Beta
    ) {
        println!("cargo:rustc-cfg=unstable_channel");
    }

    // AArch64 instruction set contains `clrex` but not `ldrex` or `strex`; the
    // probe will succeed when we already know to deny this target from LLSC.
    if !target.starts_with("aarch64") {
        match compile_probe(ARM_LLSC_PROBE) {
            Some(status) if status.success() => println!("cargo:rustc-cfg=arm_llsc"),
            _ => {}
        }
    }

    Ok(())
}

const ARM_LLSC_PROBE: &str = r#"
#![no_std]

// `no_mangle` forces codegen, which makes llvm check the contents of the `asm!` macro
#[no_mangle]
unsafe fn asm() {
    core::arch::asm!("clrex");
}
"#;

// this function was taken from anyhow v1.0.63 build script
// https://crates.io/crates/anyhow/1.0.63 (last visited 2022-09-02)
// the code is licensed under 'MIT or APACHE-2.0'
fn compile_probe(source: &str) -> Option<ExitStatus> {
    let rustc = env::var_os("RUSTC")?;
    let out_dir = env::var_os("OUT_DIR")?;
    let probefile = Path::new(&out_dir).join("probe.rs");
    fs::write(&probefile, source).ok()?;

    // Make sure to pick up Cargo rustc configuration.
    let mut cmd = if let Some(wrapper) = env::var_os("RUSTC_WRAPPER") {
        let mut cmd = Command::new(wrapper);
        // The wrapper's first argument is supposed to be the path to rustc.
        cmd.arg(rustc);
        cmd
    } else {
        Command::new(rustc)
    };

    cmd.stderr(Stdio::null())
        .arg("--edition=2018")
        .arg("--crate-name=probe")
        .arg("--crate-type=lib")
        .arg("--out-dir")
        .arg(out_dir)
        .arg(probefile);

    if let Some(target) = env::var_os("TARGET") {
        cmd.arg("--target").arg(target);
    }

    // If Cargo wants to set RUSTFLAGS, use that.
    if let Ok(rustflags) = env::var("CARGO_ENCODED_RUSTFLAGS") {
        if !rustflags.is_empty() {
            for arg in rustflags.split('\x1f') {
                cmd.arg(arg);
            }
        }
    }

    cmd.status().ok()
}
