extern crate bit_vec;

#[macro_use]
extern crate type_operators;


use std::collections::HashMap;

use bit_vec::BitVec;


// A representation of a Smallfuck program. This isn't a very optimized
// representation - since the runtime implementation is meant for checking the
// type-level implementation, I decided it'd be best to just mirror the
// type-level version as best as possible. So, we have a fairly conventional
// AST here.
//
// - `Empty` - a program which does nothing. When the interpreter hits this, it
//   halts if there's nothing left to run.
// - `Left`/`Right` - pointer decrement/increment.
// - `Flip` - flip the bit at the pointer.
// - `Loop(P, Q)` - if the bit at the pointer is zero, run `P` then check again;
//   else, continue with `Q`.
#[derive(Debug)]
pub enum Program {
    Empty,
    Left(Box<Program>),
    Right(Box<Program>),
    Flip(Box<Program>),
    Loop(Box<(Program, Program)>),
}


// This is the `State` object output by `reify`ing the output of the type-level
// implementation. We keep track of every bit in the type-level implementation,
// so here we use a `BitVec` rather than a sparse representation.
#[derive(Debug)]
pub struct State {
    loc: usize,
    bits: BitVec,
}


// The type-level implementation uses a zipper list, which means it doesn't have
// to keep track of the pointer. However, in our runtime version, it'd be very
// irritating if the pointer couldn't go negative. (I'm realizing now I could
// have just let it wrap around, but screwit, I'm not gonna rewrite this.) So
// we use a `HashMap` which allows us to map `isize` to `bool`
// without much fanfare, efficiency, or effort.
#[derive(Debug)]
pub struct SparseState {
    loc: isize,
    bits: HashMap<isize, bool>,
}


impl Program {
    // A "big step" here completely executes a Smallfuck program with respect to
    // some given state.
    fn big_step(&self, state: &mut SparseState) {
        use self::Program::*;

        match *self {
            Empty => {
                // No modifications to the program; stop recursing. We're done.
            }
            Left(ref next) => {
                // Pointer decrement.
                state.loc -= 1;
                println!("< | pointer from {} to {}. {:?}",
                         state.loc + 1,
                         state.loc,
                         state);
                // We're done. Next instruction! Since we're representing our
                // program with an AST-like format, we'll keep going using
                // recursion.
                next.big_step(state);
            }
            Right(ref next) => {
                // Pointer increment.
                state.loc += 1;
                next.big_step(state);
            }
            Flip(ref next) => {
                // Flip the bit at the pointer.
                {
                    // We're working with a `HashMap`; thus, an entry might not
                    // exist. So, we insert `false` if it's not.
                    let cell = state.bits.entry(state.loc).or_insert(false);
                    *cell = !*cell;
                }
                next.big_step(state);
            }
            Loop(ref boxed) => {
                // Loop - the most complex instruction. We check the bit at the
                // pointer. If it's zero (`false`), we continue; if it's one
                // (`true`), then we run the body of the loop again.
                let &(ref block, ref next) = boxed.as_ref();
                if *state.bits.get(&state.loc).unwrap_or(&false) {
                    // Case 1: zero - run the loop body.
                    block.big_step(state);
                    // Looping means we re-check. Note that we're *recursing*
                    // here, with the exact same program we started with, *but*
                    // a different state.
                    self.big_step(state);
                } else {
                    // Case 2: one - we continue onwards.
                    next.big_step(state);
                }
            }
        }
    }


    // Convenience function to run a program without having to write out the
    // state allocation boilerplate.
    fn run(&self) -> SparseState {
        let mut state: SparseState = SparseState {
            loc: 0,
            bits: HashMap::new(),
        };

        self.big_step(&mut state);

        state
    }
}


// Here we get to the fun part! This is all done using the `type_operators!`
// macro, which is defined in the [type-operators](https://crates.io/crates/type-operators)
// crate. For more precise information, please read the documentation. I plan to
// eventually make a blog post about this implementation to explain better in-depth.
type_operators! {
    // This weirdness is just a hack to make the macro work. Rust doesn't have
    // the ability to generate arbitrary unique symbols in macros, so we provide
    // a list of our own.
    [A, B, C, D, E]
    
    // `ProgramTy` is the type-level representation of our Smallfuck program.
    // This compiles to a trait definition - `ProgramTy`, with one function,
    // `reify()`. `reify()` is defined inductively over these five types, as
    // shown below - I think it's fairly readable and straightforward. `Empty`,
    // `Left<P>`, `Right<P>`, `Flip<P>`, and `Loop<P, Q>` are all structs
    // which are generated by the `type_operators!` macro along with the
    // `ProgramTy` trait.
    concrete ProgramTy => Program {
        Empty => Program::Empty,
        Left(P: ProgramTy = Empty) => Program::Left(Box::new(P)),
        Right(P: ProgramTy = Empty) => Program::Right(Box::new(P)),
        Flip(P: ProgramTy = Empty) => Program::Flip(Box::new(P)),
        Loop(P: ProgramTy = Empty, Q: ProgramTy = Empty) => Program::Loop(Box::new((P, Q))),
    }

    // This compiles to a trait `Bit` and two unit structs - `F` and `T`.
    // Once again, `reify` is added to the `Bit` trait and allows us to turn
    // our `Bit`s into `bool`s. Useful for producing output to check against
    // our runtime Smallfuck implementation!
    concrete Bit => bool {
        F => false,
        T => true,
    }

    // We use a zipper list to represent the Smallfuck memory space. This is one
    // side of that zipper list - it's a straightforward cons-list of bits. It
    // can be `reify`'d into a `BitVec`.
    concrete List => BitVec {
        Nil => BitVec::new(),
        Cons(B: Bit, L: List = Nil) => { let mut tail = L; tail.push(B); tail },
    }

    // `StateTy` is the type-level representation of the state of the Smallfuck
    // interpreter. It's a zipper list, so we've got a left-list, `L` - our
    // current bit, `C` - and our right-list, `R`.
    concrete StateTy => State {
        St(L: List, C: Bit, R: List) => {
            let mut bits = L;
            let loc = bits.len();
            bits.push(C);
            bits.extend(R.into_iter().rev());

            State {
                loc: loc,
                bits: bits,
            }
        },
    }

    // This produces a trait `Running<StateTy>: ProgramTy` with an associated
    // type `Output: StateTy`. `Run` is a type synonym defined as
    // `type Run<P, S> = <P as Running<S>>::Output;`. 
    //
    // Now we get into a rather nasty bunch of case analysis. Heeere we go!
    // - Pointer decrement, left cons-list is nil: create a new `F`
    // - Pointer increment, right cons-list is nil: create a new `F`
    // - Pointer decrement, left cons-list is cons: move the value out of the left cons-list
    // - Pointer increment, right cons-list is cons: move the value out of the right cons-list
    // - Flip current bit: current bit is `F` - change to `T`
    // - Flip current bit: current bit is `T` - change to `F`
    // - Loop, current bit is `F` - continue
    // - Loop, current bit is `T` - run the body, then recursively run the same
    //   instructions with the new state
    // - Empty: return the state unmodified, and don't recurse
    (Run) Running(ProgramTy, StateTy): StateTy {
        forall (P: ProgramTy, C: Bit, R: List) {
            [(Left P), (St Nil C R)] => (# P (St Nil F (Cons C R)))
        }
        forall (P: ProgramTy, L: List, C: Bit) {
            [(Right P), (St L C Nil)] => (# P (St (Cons C L) F Nil))
        }
        forall (P: ProgramTy, L: List, C: Bit, N: Bit, R: List) {
            [(Left P), (St (Cons N L) C R)] => (# P (St L N (Cons C R)))
            [(Right P), (St L C (Cons N R))] => (# P (St (Cons C L) N R))
        }
        forall (P: ProgramTy, L: List, R: List) {
            [(Flip P), (St L F R)] => (# P (St L T R))
            [(Flip P), (St L T R)] => (# P (St L F R))
        }
        forall (P: ProgramTy, Q: ProgramTy, L: List, R: List) {
            [(Loop P Q), (St L F R)] => (# Q (St L F R))
            [(Loop P Q), (St L T R)] => (# (Loop P Q) (# P (St L T R)))
        }
        forall (S: StateTy) {
            [Empty, S] => S
        }
    }
}


// A Smallfuck state which is filled with `F` bits - a clean slate.
pub type Blank = St<Nil, F, Nil>;


// Convert nicely formatted Smallfuck into type-encoded Smallfuck.
macro_rules! sf {
    (< $($prog:tt)*) => { Left<sf!($($prog)*)> };
    (> $($prog:tt)*) => { Right<sf!($($prog)*)> };
    (* $($prog:tt)*) => { Flip<sf!($($prog)*)> };
    ([$($prog:tt)*]) => { Loop<sf!($($prog)*)> };
    () => { Empty };
}


macro_rules! sf_test {
    ($($test_name:ident $prog:tt)*) => {
         $(
            #[test]
            fn $test_name() {
                let prog = <sf! $prog as ProgramTy>::reify();

                let typelevel_out = <Run<sf! $prog, Blank> as StateTy>::reify();
                let runtime_out = prog.run();

                println!("Program: {:?}", prog);
                println!("Type-level output: {:?}", typelevel_out);
                println!("Runtime output: {:?}", runtime_out);

                let offset = runtime_out.loc - (typelevel_out.loc as isize);

                for (i, b1) in typelevel_out.bits.into_iter().enumerate() {
                    let b2 = *runtime_out.bits.get(&(i as isize + offset)).unwrap_or(&false);
                    println!("[{}] {} == {}",
                            i,
                            if b1 { "1" } else { "0" },
                            if b2 { "1" } else { "0" });
                    assert_eq!(b1, b2);
                }
            }
         )*
    }
}


sf_test! {
    back_and_forth {
        > * > * > * [ * < ]
    }
    forth_and_back {
        < * < * < * [ * > ]
    }
}
