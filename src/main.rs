use std::collections::HashSet;

use algebra::{orbit_of_element, D3h, Finite, ThreeInputBooleanFunction};

fn main() {
    let mut orbits: Vec<HashSet<ThreeInputBooleanFunction>> = Vec::new();
    for element in ThreeInputBooleanFunction::all() {
        let orbit = orbit_of_element::<D3h, _>(element);
        if !orbits.contains(&orbit) {
            orbits.push(orbit);
        }
    }
    // show orbit index for every element
    // for element in ThreeInputBooleanFunction::all() {
    //     let index = orbits
    //         .iter()
    //         .position(|orbit| orbit.contains(&element))
    //         .unwrap();
    //     println!("{}: {:?}", index, element);
    // }

    // show number of orbits
    println!("Number of orbits: {}", orbits.len());

    // for every orbit in orbits: print out their elements (in python syntax)
    // println!("[");
    // for orbit in orbits {
    //     let mut elements: Vec<String> = Vec::new();
    //     for element in orbit {
    //         elements.push(format!("\"{:08b}\"", element.to_byte()));
    //     }
    //     println!("[{}],\n", elements.join(", "));
    // }
    // println!("]");
}
