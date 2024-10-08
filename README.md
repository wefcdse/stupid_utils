## Description

A crate that provides some simple and maybe stupid or useful tools

Most of the features are zero-cost, all non-zero-cost feature can be disabled by `disable_non_zerocost` feature flag.

All dependencies and build script are optional, so the code can be simply copy and paste to another project to use.

## Example

```rust
    use std::collections::HashMap;
    use stupid_utils::prelude::*;

    let a = HashMap::new().mutable_init(|m| {
        m.insert(1, 4.box_up());
        m.insert(
            2,
            Some(9)
                .map_value(|v| match v {
                    Some(v) => v,
                    None => 3,
                })
                .box_up(),
        );
        let cond = true;
        m.insert(cond.select(3, 4), select(cond, 3, 4).box_up());
    });

    let b = {
        let mut m = HashMap::new();
        m.insert(1, Box::new(4));
        m.insert(
            2,
            Box::new({
                let v = Some(9);
                match v {
                    Some(v) => v,
                    None => 3,
                }
            }),
        );
        let cond = true;
        m.insert(if cond { 3 } else { 4 }, Box::new(if cond { 3 } else { 4 }));
        m
    };

    assert_eq!(a, b);
   

```
