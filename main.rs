fn main() {
    let a = String::from("Inpsibol");
    let b = a;

    a.push('!');

    println!("{b}");

    drop(a);

    println!("{b}");

    return;

    println!("Hello World");
}
