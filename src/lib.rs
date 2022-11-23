#[macro_use]
extern crate quickcheck;

use alga::general::{AbstractGroup, AbstractMagma, Identity, Multiplicative, TwoSidedInverse};
use alga_derive::Alga;

use approx::{AbsDiffEq, RelativeEq};
use quickcheck::{Arbitrary, Gen};
use std::collections::HashSet;
use std::hash::{Hash, Hasher};
use std::{
    collections::HashMap,
    fmt::{Debug, Error, Formatter},
};

pub trait Finite: Eq + Hash + Sized + Clone {
    fn all() -> Vec<Self>;
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Alga)]
#[alga_traits(Group(Multiplicative))]
#[alga_quickcheck()]
pub enum D3 {
    E,
    R,
    R2,
    S,
    SR,
    SR2,
}

impl AbsDiffEq for D3 {
    type Epsilon = ();

    fn default_epsilon() {}

    fn abs_diff_eq(&self, other: &Self, _epsilon: Self::Epsilon) -> bool {
        self == other
    }
}

impl RelativeEq for D3 {
    fn default_max_relative() {}

    fn relative_eq(
        &self,
        other: &Self,
        _epsilon: Self::Epsilon,
        _max_relative: Self::Epsilon,
    ) -> bool {
        self == other
    }
}

impl Arbitrary for D3 {
    fn arbitrary(g: &mut Gen) -> Self {
        g.choose(&[D3::E, D3::R, D3::R2, D3::S, D3::SR, D3::SR2])
            .unwrap()
            .clone()
    }
}

impl AbstractMagma<Multiplicative> for D3 {
    fn operate(&self, right: &Self) -> Self {
        match (self, right) {
            (D3::E, _) => right.clone(),
            (_, D3::E) => self.clone(),
            (D3::R, D3::R) => D3::R2,
            (D3::R, D3::R2) => D3::E,
            (D3::R, D3::S) => D3::SR2,
            (D3::R, D3::SR) => D3::S,
            (D3::R, D3::SR2) => D3::SR,
            (D3::R2, D3::R) => D3::E,
            (D3::R2, D3::R2) => D3::R,
            (D3::R2, D3::S) => D3::SR,
            (D3::R2, D3::SR) => D3::SR2,
            (D3::R2, D3::SR2) => D3::S,
            (D3::S, D3::R) => D3::SR,
            (D3::S, D3::R2) => D3::SR2,
            (D3::S, D3::S) => D3::E,
            (D3::S, D3::SR) => D3::R,
            (D3::S, D3::SR2) => D3::R2,
            (D3::SR, D3::R) => D3::SR2,
            (D3::SR, D3::R2) => D3::S,
            (D3::SR, D3::S) => D3::R2,
            (D3::SR, D3::SR) => D3::E,
            (D3::SR, D3::SR2) => D3::R,
            (D3::SR2, D3::R) => D3::S,
            (D3::SR2, D3::R2) => D3::SR,
            (D3::SR2, D3::S) => D3::R,
            (D3::SR2, D3::SR) => D3::R2,
            (D3::SR2, D3::SR2) => D3::E,
        }
    }
}
impl Identity<Multiplicative> for D3 {
    fn identity() -> Self {
        D3::E
    }
}
impl TwoSidedInverse<Multiplicative> for D3 {
    fn two_sided_inverse(&self) -> Self {
        match self {
            D3::E => D3::E,
            D3::R => D3::R2,
            D3::R2 => D3::R,
            D3::S => D3::S,
            D3::SR => D3::SR,
            D3::SR2 => D3::SR2,
        }
    }
}

impl Finite for D3 {
    fn all() -> Vec<D3> {
        vec![D3::E, D3::R, D3::R2, D3::S, D3::SR, D3::SR2]
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Alga)]
#[alga_traits(Group(Multiplicative))]
#[alga_quickcheck()]
pub enum S3 {
    ABC,
    BCA,
    CAB,
    ACB,
    BAC,
    CBA,
}

impl AbsDiffEq for S3 {
    type Epsilon = ();

    fn default_epsilon() {}

    fn abs_diff_eq(&self, other: &Self, _epsilon: Self::Epsilon) -> bool {
        self == other
    }
}

impl RelativeEq for S3 {
    fn default_max_relative() {}

    fn relative_eq(
        &self,
        other: &Self,
        _epsilon: Self::Epsilon,
        _max_relative: Self::Epsilon,
    ) -> bool {
        self == other
    }
}

impl Arbitrary for S3 {
    fn arbitrary(g: &mut Gen) -> Self {
        g.choose(&[S3::ABC, S3::BCA, S3::CAB, S3::ACB, S3::BAC, S3::CBA])
            .unwrap()
            .clone()
    }
}

impl S3 {
    fn s3_to_d3(&self) -> D3 {
        match self {
            S3::ABC => D3::E,
            S3::BCA => D3::R,
            S3::CAB => D3::R2,
            S3::ACB => D3::S,
            S3::BAC => D3::SR,
            S3::CBA => D3::SR2,
        }
    }

    fn d3_to_s3(d3: D3) -> S3 {
        match d3 {
            D3::E => S3::ABC,
            D3::R => S3::BCA,
            D3::R2 => S3::CAB,
            D3::S => S3::ACB,
            D3::SR => S3::BAC,
            D3::SR2 => S3::CBA,
        }
    }
}

impl AbstractMagma<Multiplicative> for S3 {
    fn operate(&self, right: &Self) -> Self {
        S3::d3_to_s3(AbstractMagma::operate(&self.s3_to_d3(), &right.s3_to_d3()))
    }
}

impl Identity<Multiplicative> for S3 {
    fn identity() -> Self {
        S3::ABC
    }
}

impl TwoSidedInverse<Multiplicative> for S3 {
    fn two_sided_inverse(&self) -> Self {
        S3::d3_to_s3(self.s3_to_d3().two_sided_inverse())
    }
}

impl Finite for S3 {
    fn all() -> Vec<S3> {
        vec![S3::ABC, S3::BCA, S3::CAB, S3::ACB, S3::BAC, S3::CBA]
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Alga)]
#[alga_traits(Group(Multiplicative))]
#[alga_quickcheck()]
enum Z2 {
    NegOne,
    One,
}

impl AbsDiffEq for Z2 {
    type Epsilon = ();

    fn default_epsilon() {}

    fn abs_diff_eq(&self, other: &Self, _epsilon: Self::Epsilon) -> bool {
        self == other
    }
}

impl RelativeEq for Z2 {
    fn default_max_relative() {}

    fn relative_eq(
        &self,
        other: &Self,
        _epsilon: Self::Epsilon,
        _max_relative: Self::Epsilon,
    ) -> bool {
        self == other
    }
}

impl Arbitrary for Z2 {
    fn arbitrary(g: &mut Gen) -> Self {
        g.choose(&[Z2::NegOne, Z2::One]).unwrap().clone()
    }
}

impl AbstractMagma<Multiplicative> for Z2 {
    fn operate(&self, right: &Self) -> Self {
        match (self, right) {
            (Z2::NegOne, Z2::NegOne) => Z2::One,
            (Z2::NegOne, Z2::One) => Z2::NegOne,
            (Z2::One, Z2::NegOne) => Z2::NegOne,
            (Z2::One, Z2::One) => Z2::One,
        }
    }
}

impl Identity<Multiplicative> for Z2 {
    fn identity() -> Self {
        Z2::One
    }
}

impl TwoSidedInverse<Multiplicative> for Z2 {
    fn two_sided_inverse(&self) -> Self {
        match self {
            Z2::NegOne => Z2::NegOne,
            Z2::One => Z2::One,
        }
    }
}

impl Finite for Z2 {
    fn all() -> Vec<Z2> {
        vec![Z2::NegOne, Z2::One]
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Alga)]
#[alga_traits(Group(Multiplicative))]
#[alga_quickcheck()]
pub struct D3h(D3, Z2);

impl AbsDiffEq for D3h {
    type Epsilon = ();

    fn default_epsilon() {}

    fn abs_diff_eq(&self, other: &Self, _epsilon: Self::Epsilon) -> bool {
        self == other
    }
}

impl RelativeEq for D3h {
    fn default_max_relative() {}

    fn relative_eq(
        &self,
        other: &Self,
        _epsilon: Self::Epsilon,
        _max_relative: Self::Epsilon,
    ) -> bool {
        self == other
    }
}

impl Arbitrary for D3h {
    fn arbitrary(g: &mut Gen) -> Self {
        D3h(D3::arbitrary(g), Z2::arbitrary(g))
    }
}

impl AbstractMagma<Multiplicative> for D3h {
    fn operate(&self, right: &Self) -> Self {
        D3h(
            AbstractMagma::operate(&self.0, &right.0),
            AbstractMagma::operate(&self.1, &right.1),
        )
    }
}

impl Identity<Multiplicative> for D3h {
    fn identity() -> Self {
        D3h(D3::identity(), Z2::identity())
    }
}

impl TwoSidedInverse<Multiplicative> for D3h {
    fn two_sided_inverse(&self) -> Self {
        D3h(self.0.two_sided_inverse(), self.1.two_sided_inverse())
    }
}

impl Finite for D3h {
    fn all() -> Vec<D3h> {
        let mut all = Vec::new();
        for d3 in D3::all() {
            for z2 in Z2::all() {
                all.push(D3h(d3.clone(), z2));
            }
        }
        all
    }
}

pub struct ThreeInputBooleanFunction(Box<dyn Fn(bool, bool, bool) -> bool>);

impl PartialEq for ThreeInputBooleanFunction {
    fn eq(&self, other: &Self) -> bool {
        self.0(true, true, true) == other.0(true, true, true)
            && self.0(true, true, false) == other.0(true, true, false)
            && self.0(true, false, true) == other.0(true, false, true)
            && self.0(true, false, false) == other.0(true, false, false)
            && self.0(false, true, true) == other.0(false, true, true)
            && self.0(false, true, false) == other.0(false, true, false)
            && self.0(false, false, true) == other.0(false, false, true)
            && self.0(false, false, false) == other.0(false, false, false)
    }
}

impl Eq for ThreeInputBooleanFunction {}

impl ThreeInputBooleanFunction {
    pub fn from_byte(byte: u8) -> Self {
        ThreeInputBooleanFunction(Box::new(move |a, b, c| {
            let mut result = 0_u8;
            if a {
                result += 1;
            }
            if b {
                result += 2;
            }
            if c {
                result += 4;
            }
            (byte & (1 << result)) != 0
        }))
    }

    pub fn to_byte(&self) -> u8 {
        let mut result = 0_u8;
        for bool1 in &[true, false] {
            for bool2 in &[true, false] {
                for bool3 in &[true, false] {
                    if self.0(*bool1, *bool2, *bool3) {
                        result |= 1
                            << (if *bool1 { 1 } else { 0 }
                                + if *bool2 { 2 } else { 0 }
                                + if *bool3 { 4 } else { 0 });
                    }
                }
            }
        }
        result
    }
}

impl Hash for ThreeInputBooleanFunction {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.to_byte().hash(state);
    }
}

impl Debug for ThreeInputBooleanFunction {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        let byte = self.to_byte();
        // for all inputs, print the output
        write!(f, "{:08b}: ", byte)?;
        write!(f, "ThreeInputBooleanFunction {{")?;
        for a in &[true, false] {
            for b in &[true, false] {
                for c in &[true, false] {
                    write!(f, "({}, {}, {}) -> {}, ", a, b, c, self.0(*a, *b, *c))?;
                }
            }
        }
        write!(f, "}}")
    }
}

impl Clone for ThreeInputBooleanFunction {
    fn clone(&self) -> Self {
        // call the function to find out what it is
        let mut table = HashMap::new();
        for a in &[true, false] {
            for b in &[true, false] {
                for c in &[true, false] {
                    table.insert((*a, *b, *c), self.0(*a, *b, *c));
                }
            }
        }
        ThreeInputBooleanFunction(Box::new(move |a, b, c| table[&(a, b, c)]))
    }
}

impl Finite for ThreeInputBooleanFunction {
    fn all() -> Vec<ThreeInputBooleanFunction> {
        let mut result = Vec::new();
        for byte in 0_u8..=255 {
            let function = ThreeInputBooleanFunction::from_byte(byte);
            result.push(function);
        }
        result
    }
}

mod tests {
    use crate::{Finite, ThreeInputBooleanFunction};

    #[test]
    fn list_of_all_functions_pairwise_distinct() {
        let functions = ThreeInputBooleanFunction::all();
        for i in 0..functions.len() {
            for j in 0..functions.len() {
                if i != j {
                    assert_ne!(functions[i], functions[j]);
                }
            }
        }
    }

    #[test]
    fn two_calls_generate_same_functions() {
        let functions1 = ThreeInputBooleanFunction::all();
        let functions2 = ThreeInputBooleanFunction::all();
        assert_eq!(functions1, functions2);
    }

    #[test]
    fn to_and_from_byte() {
        let functions = ThreeInputBooleanFunction::all();
        for function in functions {
            let byte = function.to_byte();
            let function2 = ThreeInputBooleanFunction::from_byte(byte);
            assert_eq!(function, function2);
        }
    }
}

pub trait Operation<M>: AbstractGroup<Multiplicative> {
    fn operate(self, right: M) -> M;
}

impl Operation<ThreeInputBooleanFunction> for Z2 {
    fn operate(self, right: ThreeInputBooleanFunction) -> ThreeInputBooleanFunction {
        ThreeInputBooleanFunction(Box::new(move |a, b, c| match self {
            Z2::NegOne => right.0(!a, !b, !c),
            Z2::One => right.0(a, b, c),
        }))
    }
}

impl Operation<ThreeInputBooleanFunction> for D3 {
    fn operate(self, right: ThreeInputBooleanFunction) -> ThreeInputBooleanFunction {
        ThreeInputBooleanFunction(Box::new(move |a, b, c| match S3::d3_to_s3(self.clone()) {
            S3::ABC => right.0(a, b, c),
            S3::BCA => right.0(b, c, a),
            S3::CAB => right.0(c, a, b),
            S3::ACB => right.0(a, c, b),
            S3::BAC => right.0(b, a, c),
            S3::CBA => right.0(c, b, a),
        }))
    }
}

impl Operation<ThreeInputBooleanFunction> for D3h {
    fn operate(self, right: ThreeInputBooleanFunction) -> ThreeInputBooleanFunction {
        ThreeInputBooleanFunction(Box::new(move |a, b, c| {
            Operation::operate(
                self.1.clone(),
                Operation::operate(self.0.clone(), right.clone()),
            )
            .0(a, b, c)
        }))
    }
}

pub fn orbit_of_element<G, M>(element: M) -> HashSet<M>
where
    G: Finite + Operation<M>,
    M: Finite,
{
    let all_group_elements = G::all();
    let mut result = HashSet::new();
    for group_element in all_group_elements {
        let new_element = Operation::operate(group_element, element.clone());
        result.insert(new_element);
    }
    result
}
