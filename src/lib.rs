extern crate bit_vec;

#[macro_use]
extern crate type_operators;


use std::collections::HashMap;

use bit_vec::BitVec;


#[derive(Debug)]
pub enum Program {
    Empty,
    Left(Box<Program>),
    Right(Box<Program>),
    Flip(Box<Program>),
    Loop(Box<(Program, Program)>),
}


#[derive(Debug)]
pub struct State {
    loc: usize,
    bits: BitVec,
}


#[derive(Debug)]
pub struct SparseState {
    loc: isize,
    bits: HashMap<isize, bool>,
}


impl Program {
    fn big_step(&self, state: &mut SparseState) {
        use self::Program::*;

        match *self {
            Empty => {}
            Left(ref next) => {
                state.loc -= 1;
                println!("< | pointer from {} to {}. {:?}",
                         state.loc + 1,
                         state.loc,
                         state);
                next.big_step(state);
            }
            Right(ref next) => {
                state.loc += 1;
                println!("> | pointer from {} to {}. {:?}",
                         state.loc - 1,
                         state.loc,
                         state);
                next.big_step(state);
            }
            Flip(ref next) => {
                {
                    let after_flip = {
                        let cell = state.bits.entry(state.loc).or_insert(false);
                        *cell = !*cell;
                        *cell
                    };
                    println!("* | cell at pointer from {} to {}. {:?}",
                             !after_flip,
                             after_flip,
                             state);
                }
                next.big_step(state);
            }
            Loop(ref boxed) => {
                let &(ref block, ref next) = boxed.as_ref();
                if *state.bits.get(&state.loc).unwrap_or(&false) {
                    println!("[ | loop block. {:?}", state);
                    block.big_step(state);
                    self.big_step(state);
                } else {
                    println!("] | loop exit. {:?}", state);
                    next.big_step(state);
                }
            }
        }
    }


    fn run(&self) -> SparseState {
        let mut state: SparseState = SparseState {
            loc: 0,
            bits: HashMap::new(),
        };

        self.big_step(&mut state);

        state
    }
}


type_operators! {
    [A, B, C, D, E]
    
    concrete ProgramTy => Program {
        Empty => Program::Empty,
        Left(P: ProgramTy = Empty) => Program::Left(Box::new(P)),
        Right(P: ProgramTy = Empty) => Program::Right(Box::new(P)),
        Flip(P: ProgramTy = Empty) => Program::Flip(Box::new(P)),
        Loop(P: ProgramTy = Empty, Q: ProgramTy = Empty) => Program::Loop(Box::new((P, Q))),
    }

    concrete Bit => bool {
        F => false,
        T => true,
    }

    concrete List => BitVec {
        Nil => BitVec::new(),
        Cons(B: Bit, L: List = Nil) => { let mut tail = L; tail.push(B); tail },
    }

    concrete StateTy => State {
        St(L: List, C: Bit, R: List) => {
            // So, everything is actually backwards here. That's because we're
            // looking at a zipper list here. So our `loc` 

            println!("bits behind: {:?}, current bit: {}, bits ahead: {:?}", L, C, R);

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


pub type Blank = St<Nil, F, Nil>;


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
