use bitint::prelude::*;

#[bitint_literals]
fn main() {
    let _x: U23 = 1234_U23;

    unresolved_function_name();

    compile_error!("whoops");

    syntax_error,
}
