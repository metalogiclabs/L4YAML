//! tryparse_rust — Minimal Rust tryparse for yaml-test-suite integration.
//!
//! Reads a YAML file, parses it via the Rust API (l4yaml::load_all), and
//! exits 0 on success, 1 on parse error.  Mirrors the Lean tryparse
//! binary exactly so the suiterunner can swap backends.
//!
//! Usage: tryparse_rust <file.yaml> [preset]
//!   preset: unlimited (default) | default | strict | permissive | safe_tags
//!
//! L4YAML_SUITE_PROTOCOL=1 adds a result marker after parsing and cleanup.
//! A process failure without that marker is not a parser rejection.

use l4yaml::LimitsPreset;

fn parse_preset(s: &str) -> Option<LimitsPreset> {
    match s {
        "unlimited" => Some(LimitsPreset::Unlimited),
        "default" => Some(LimitsPreset::Default),
        "strict" => Some(LimitsPreset::Strict),
        "permissive" => Some(LimitsPreset::Permissive),
        "safe_tags" => Some(LimitsPreset::SafeTags),
        _ => None,
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 || args.len() > 3 {
        eprintln!("Usage: tryparse_rust <file.yaml> [preset]");
        std::process::exit(2);
    }

    let preset = if args.len() == 3 {
        match parse_preset(&args[2]) {
            Some(p) => p,
            None => {
                eprintln!("Unknown preset '{}'; choose from: unlimited, default, strict, permissive, safe_tags", args[2]);
                std::process::exit(2);
            }
        }
    } else {
        LimitsPreset::Unlimited
    };

    let content = match std::fs::read_to_string(&args[1]) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Cannot open {}: {}", args[1], e);
            std::process::exit(2);
        }
    };

    l4yaml::initialize();

    let (code, marker) = match l4yaml::load_all(&content, preset) {
        Ok(_) => (0, Some("L4YAML_SUITE_ACCEPT")),
        Err(e) => {
            eprintln!("{e}");
            // Handle, encoding, and configuration faults are not deliberate
            // parser rejections even though the human CLI exits 1 for both.
            let marker = if matches!(e, l4yaml::Error::Parse(_) | l4yaml::Error::Limit(_)) {
                Some("L4YAML_SUITE_REJECT")
            } else {
                None
            };
            (1, marker)
        }
    };

    l4yaml::finalize();
    if std::env::var("L4YAML_SUITE_PROTOCOL").as_deref() == Ok("1") {
        if let Some(marker) = marker {
            println!("{marker}");
        }
    }
    std::process::exit(code);
}
