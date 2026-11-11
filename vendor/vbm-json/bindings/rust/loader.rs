// Hand-written build script (trusted, docs/trust-ledger.md T12): points the linker at libvbm_json (a directory in VBM_JSON_LIB_DIR; else the system's). It decides nothing about JSON.
fn main() {
    println!("cargo:rerun-if-env-changed=VBM_JSON_LIB_DIR");
    if let Ok(dir) = std::env::var("VBM_JSON_LIB_DIR") {
        println!("cargo:rustc-link-search=native={}", dir);
        println!("cargo:rustc-link-arg=-Wl,-rpath,{}", dir);
    }
}
