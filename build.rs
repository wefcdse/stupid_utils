use std::{env, fs, path::Path};

fn main() {
    let out_dir = env::var_os("OUT_DIR").unwrap();

    {
        let dest_path = Path::new(&out_dir).join("impl_fn_apply.rs");
        fs::write(&dest_path, gen_impl_start() + &gen_impl_extend()).unwrap();
    }
    {
        let dest_path = Path::new(&out_dir).join("struct_tuple_idx.rs");
        fs::write(&dest_path, gen_idx_ty()).unwrap();
    }
    {
        let dest_path = Path::new(&out_dir).join("impl_tuple_idx.rs");
        fs::write(&dest_path, gen_idx_impl()).unwrap();
    }
    println!("cargo::rerun-if-changed=build.rs");
}
#[macro_export]
macro_rules! mutable {
    ($name:ident) => {
        let mut $name = $name;
    };
}
#[macro_export]
macro_rules! nonmutable {
    ($name:ident) => {
        let $name = $name;
    };
}

fn gen_impl_start() -> String {
    let o = String::new();
    mutable!(o);
    for i in 1..20 {
        let mut t = String::new();
        for j in 0..=i {
            t += &format!("T{j}");
            if j != i {
                t += ",";
            }
        }
        o += &format!("impl_applyone!({});\n", t);
    }
    o
}
fn gen_impl_extend() -> String {
    let mut s = String::new();
    for i in 1..20 {
        for k in 1..=i {
            let mut t = String::new();
            for j in 0..=i {
                if j == k {
                    t += &format!("[T{j}]");
                } else {
                    t += &format!("T{j}");
                }
                if j != i {
                    t += ",";
                }
            }
            s += &format!("impl_extend!({});\n", t);
        }
    }
    s
}

fn gen_idx_ty() -> String {
    let mut s = String::new();
    for i in 0..20 {
        s += &format!("/// index tuple by {}\n", i);
        s += &format!("pub struct I{};\n", i);
    }
    s
}

fn gen_idx_impl() -> String {
    let o = String::new();
    mutable!(o);
    let len = 20;
    for i in 0..len {
        let a = String::new();
        mutable!(a);
        for j in 0..=i {
            a += &format!("T{}", j);
            if j != i {
                a += ", ";
            }
        }
        nonmutable!(a);
        for j in 0..=i {
            o += &format!("impls_ref!(I{j}, T{j}, {j}, {a});\n");
            o += &format!("impls_mut!(I{j}, T{j}, {j}, {a});\n");
        }
    }
    o
}
