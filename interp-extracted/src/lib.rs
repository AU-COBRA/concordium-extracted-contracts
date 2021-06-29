#![allow(dead_code)]
#![allow(non_camel_case_types)]
#![allow(unused_imports)]
#![allow(non_snake_case)]
#![allow(unused_variables)]

use concordium_std::*;
use concert_std::{ActionBody, ConCertDeserial, ConCertSerial, SerializedValue};
use core::marker::PhantomData;
use immutable_map::TreeMap;

fn __nat_succ(x: u64) -> u64 {
  x.checked_add(1).unwrap()
}

macro_rules! __nat_elim {
    ($zcase:expr, $pred:ident, $scase:expr, $val:expr) => {
        { let v = $val;
        if v == 0 { $zcase } else { let $pred = v - 1; $scase } }
    }
}

macro_rules! __andb { ($b1:expr, $b2:expr) => { $b1 && $b2 } }
macro_rules! __orb { ($b1:expr, $b2:expr) => { $b1 || $b2 } }

fn __pos_onebit(x: u64) -> u64 {
  x.checked_mul(2).unwrap() + 1
}

fn __pos_zerobit(x: u64) -> u64 {
  x.checked_mul(2).unwrap()
}

macro_rules! __pos_elim {
    ($p:ident, $onebcase:expr, $p2:ident, $zerobcase:expr, $onecase:expr, $val:expr) => {
        {
            let n = $val;
            if n == 1 {
                $onecase
            } else if (n & 1) == 0 {
                let $p2 = n >> 1;
                $zerobcase
            } else {
                let $p = n >> 1;
                $onebcase
            }
        }
    }
}

fn __Z_frompos(z: u64) -> i64 {
  use std::convert::TryFrom;

  i64::try_from(z).unwrap()
}

fn __Z_fromneg(z : u64) -> i64 {
  use std::convert::TryFrom;

  i64::try_from(z).unwrap().checked_neg().unwrap()
}

macro_rules! __Z_elim {
    ($zero_case:expr, $p:ident, $pos_case:expr, $p2:ident, $neg_case:expr, $val:expr) => {
        {
            let n = $val;
            if n == 0 {
                $zero_case
            } else if n < 0 {
                let $p2 = n.unsigned_abs();
                $neg_case
            } else {
                let $p = n as u64;
                $pos_case
            }
        }
    }
}

fn __N_frompos(z: u64) -> u64 {
  z
}

macro_rules! __N_elim {
    ($zero_case:expr, $p:ident, $pos_case:expr, $val:expr) => {
        { let $p = $val; if $p == 0 { $zero_case } else { $pos_case } }
    }
}

type __pair<A, B> = (A, B);

macro_rules! __pair_elim {
    ($fst:ident, $snd:ident, $body:expr, $p:expr) => {
        { let ($fst, $snd) = $p; $body }
    }
}

fn __mk_pair<A: Copy, B: Copy>(a: A, b: B) -> __pair<A, B> { (a, b) }

fn hint_app<TArg, TRet>(f: &dyn Fn(TArg) -> TRet) -> &dyn Fn(TArg) -> TRet {
  f
}

#[derive(Debug, PartialEq, Eq, Reject)]
enum InitError {
   DeserialParams,
   SerialParams,
   Error
}

#[derive(Debug, PartialEq, Eq)]
enum ReceiveError {
    DeserialMsg,
    DeserialOldState,
    SerialNewState,
    ConvertActions, // Cannot convert ConCert actions to Concordium actions
    Error
}
impl From<ReceiveError> for concordium_std::Reject {
  fn from(_ : ReceiveError) -> Self {
    ().into()
  }
}

#[derive(Clone, ConCertSerial, ConCertDeserial, PartialEq)]
pub enum List<'a, A> {
  nil(PhantomData<&'a A>),
  cons(PhantomData<&'a A>, A, &'a List<'a, A>)
}

#[derive(Clone, ConCertSerial, ConCertDeserial, PartialEq)]
pub enum Chain<'a> {
  build_chain(PhantomData<&'a ()>, u64, u64, u64)
}

type Address<'a> = concordium_std::Address;

type Amount<'a> = i64;

#[derive(Clone, ConCertSerial, ConCertDeserial, PartialEq)]
pub enum ContractCallContext<'a> {
  build_ctx(PhantomData<&'a ()>, Address<'a>, Address<'a>, Amount<'a>, Amount<'a>)
}

#[derive(Clone, ConCertSerial, ConCertDeserial, PartialEq)]
pub enum Value<'a> {
  BVal(PhantomData<&'a ()>, bool),
  ZVal(PhantomData<&'a ()>, i64)
}

type Storage<'a> = &'a List<'a, &'a Value<'a>>;

#[derive(Clone, ConCertSerial, ConCertDeserial, PartialEq)]
pub enum Op<'a> {
  Add(PhantomData<&'a ()>),
  Sub(PhantomData<&'a ()>),
  Mult(PhantomData<&'a ()>),
  Lt(PhantomData<&'a ()>),
  Le(PhantomData<&'a ()>),
  Equal(PhantomData<&'a ()>)
}

#[derive(Clone, ConCertSerial, ConCertDeserial, PartialEq)]
pub enum Instruction<'a> {
  IPushZ(PhantomData<&'a ()>, i64),
  IPushB(PhantomData<&'a ()>, bool),
  IObs(PhantomData<&'a ()>, __pair<&'a String, i64>),
  IIf(PhantomData<&'a ()>),
  IElse(PhantomData<&'a ()>),
  IEndIf(PhantomData<&'a ()>),
  IOp(PhantomData<&'a ()>, &'a Op<'a>)
}

type Ext_map<'a> = &'a immutable_map::TreeMap<(&'a String, i64), Value<'a>>;

type Msg<'a> = __pair<&'a List<'a, &'a Instruction<'a>>, Ext_map<'a>>;

struct Program {
  __alloc: bumpalo::Bump,
}

impl<'a> Program {
fn new() -> Self {
  Program {
    __alloc: bumpalo::Bump::new(),
  }
}

fn alloc<T>(&'a self, t: T) -> &'a T {
  self.__alloc.alloc(t)
}

fn closure<TArg, TRet>(&'a self, F: impl Fn(TArg) -> TRet + 'a) -> &'a dyn Fn(TArg) -> TRet {
  self.__alloc.alloc(F)
}

fn init(&'a self, chain: &'a Chain<'a>, ctx: &'a ContractCallContext<'a>, setup: ()) -> Option<Storage<'a>> {
  Some(
    self.alloc(
      List::nil(
        PhantomData)))
}
fn init__curried(&'a self) -> &'a dyn Fn(&'a Chain<'a>) -> &'a dyn Fn(&'a ContractCallContext<'a>) -> &'a dyn Fn(()) -> Option<Storage<'a>> {
  self.closure(move |chain| {
    self.closure(move |ctx| {
      self.closure(move |setup| {
        self.init(
          chain,
          ctx,
          setup)
      })
    })
  })
}

fn eqb(&'a self, a: i64, b: i64) -> bool { a == b }
fn eqb__curried(&'a self) -> &'a dyn Fn(i64) -> &'a dyn Fn(i64) -> bool {
  self.closure(move |x| {
    self.closure(move |y| {
      self.eqb(
        x,
        y)
    })
  })
}

fn continue_(&'a self, i: i64) -> bool {
  self.eqb(
    i,
    0)
}
fn continue___curried(&'a self) -> &'a dyn Fn(i64) -> bool {
  self.closure(move |i| {
    self.continue_(
      i)
  })
}

fn lookup<V>(&'a self, key : (&'a String,i64) , m : &'a immutable_map::TreeMap<(&'a String,i64), V>) -> Option<&'a V> {
   m.get(&key)
}
fn lookup__curried(&'a self) -> &'a dyn Fn(__pair<&'a String, i64>) -> &'a dyn Fn(Ext_map<'a>) -> Option<&'a Value<'a>> {
  self.closure(move |k| {
    self.closure(move |m| {
      self.lookup(
        k,
        m)
    })
  })
}

fn bool_to_cond(&'a self, b: bool) -> i64 {
  match b {
    true => {
      0
    },
    false => {
      __Z_frompos(
        1)
    },
  }
}
fn bool_to_cond__curried(&'a self) -> &'a dyn Fn(bool) -> i64 {
  self.closure(move |b| {
    self.bool_to_cond(
      b)
  })
}

fn add(&'a self, a: i64, b: i64) -> i64 { a.checked_add(b).unwrap() }
fn add__curried(&'a self) -> &'a dyn Fn(i64) -> &'a dyn Fn(i64) -> i64 {
  self.closure(move |x| {
    self.closure(move |y| {
      self.add(
        x,
        y)
    })
  })
}

fn flip(&'a self, i: i64) -> i64 {
  match self.eqb(
          i,
          0) {
    true => {
      __Z_frompos(
        1)
    },
    false => {
      match self.eqb(
              i,
              __Z_frompos(
                1)) {
        true => {
          0
        },
        false => {
          i
        },
      }
    },
  }
}
fn flip__curried(&'a self) -> &'a dyn Fn(i64) -> i64 {
  self.closure(move |i| {
    self.flip(
      i)
  })
}

fn leb(&'a self, a: i64, b: i64) -> bool { a <= b }
fn leb__curried(&'a self) -> &'a dyn Fn(i64) -> &'a dyn Fn(i64) -> bool {
  self.closure(move |x| {
    self.closure(move |y| {
      self.leb(
        x,
        y)
    })
  })
}

fn sub(&'a self, a: i64, b: i64) -> i64 { a.checked_sub(b).unwrap() }
fn sub__curried(&'a self) -> &'a dyn Fn(i64) -> &'a dyn Fn(i64) -> i64 {
  self.closure(move |m| {
    self.closure(move |n| {
      self.sub(
        m,
        n)
    })
  })
}

fn reset_decrement(&'a self, i: i64) -> i64 {
  match self.leb(
          i,
          __Z_frompos(
            1)) {
    true => {
      0
    },
    false => {
      self.sub(
        i,
        __Z_frompos(
          1))
    },
  }
}
fn reset_decrement__curried(&'a self) -> &'a dyn Fn(i64) -> i64 {
  self.closure(move |i| {
    self.reset_decrement(
      i)
  })
}

fn mul(&'a self, a: i64, b: i64) -> i64 { a.checked_mul(b).unwrap() }
fn mul__curried(&'a self) -> &'a dyn Fn(i64) -> &'a dyn Fn(i64) -> i64 {
  self.closure(move |x| {
    self.closure(move |y| {
      self.mul(
        x,
        y)
    })
  })
}

fn ltb(&'a self, a: i64, b: i64) -> bool { a < b }
fn ltb__curried(&'a self) -> &'a dyn Fn(i64) -> &'a dyn Fn(i64) -> bool {
  self.closure(move |x| {
    self.closure(move |y| {
      self.ltb(
        x,
        y)
    })
  })
}

fn interp(&'a self, ext: Ext_map<'a>, insts: &'a List<'a, &'a Instruction<'a>>, s: &'a List<'a, &'a Value<'a>>, cond: i64) -> Option<&'a List<'a, &'a Value<'a>>> {
  match insts {
    &List::nil(_) => {
      Some(
        s)
    },
    &List::cons(_, hd, inst0) => {
      match hd {
        &Instruction::IPushZ(_, i) => {
          match self.continue_(
                  cond) {
            true => {
              self.interp(
                ext,
                inst0,
                self.alloc(
                  List::cons(
                    PhantomData,
                    self.alloc(
                      Value::ZVal(
                        PhantomData,
                        i)),
                    s)),
                cond)
            },
            false => {
              self.interp(
                ext,
                inst0,
                s,
                cond)
            },
          }
        },
        &Instruction::IPushB(_, b) => {
          match self.continue_(
                  cond) {
            true => {
              self.interp(
                ext,
                inst0,
                self.alloc(
                  List::cons(
                    PhantomData,
                    self.alloc(
                      Value::BVal(
                        PhantomData,
                        b)),
                    s)),
                cond)
            },
            false => {
              self.interp(
                ext,
                inst0,
                s,
                cond)
            },
          }
        },
        &Instruction::IObs(_, p) => {
          match self.continue_(
                  cond) {
            true => {
              match self.lookup(
                      p,
                      ext) {
                Some(v) => {
                  self.interp(
                    ext,
                    inst0,
                    self.alloc(
                      List::cons(
                        PhantomData,
                        v,
                        s)),
                    cond)
                },
                None => {
                  None
                },
              }
            },
            false => {
              self.interp(
                ext,
                inst0,
                s,
                cond)
            },
          }
        },
        &Instruction::IIf(_) => {
          match self.eqb(
                  cond,
                  0) {
            true => {
              match s {
                &List::nil(_) => {
                  None
                },
                &List::cons(_, v, s0) => {
                  match v {
                    &Value::BVal(_, b) => {
                      self.interp(
                        ext,
                        inst0,
                        s0,
                        self.bool_to_cond(
                          b))
                    },
                    &Value::ZVal(_, z) => {
                      None
                    },
                  }
                },
              }
            },
            false => {
              self.interp(
                ext,
                inst0,
                s,
                self.add(
                  __Z_frompos(
                    1),
                  cond))
            },
          }
        },
        &Instruction::IElse(_) => {
          self.interp(
            ext,
            inst0,
            s,
            self.flip(
              cond))
        },
        &Instruction::IEndIf(_) => {
          self.interp(
            ext,
            inst0,
            s,
            self.reset_decrement(
              cond))
        },
        &Instruction::IOp(_, op) => {
          match self.continue_(
                  cond) {
            true => {
              match op {
                &Op::Add(_) => {
                  match s {
                    &List::nil(_) => {
                      None
                    },
                    &List::cons(_, v, l) => {
                      match v {
                        &Value::BVal(_, b) => {
                          None
                        },
                        &Value::ZVal(_, i) => {
                          match l {
                            &List::nil(_) => {
                              None
                            },
                            &List::cons(_, v0, s0) => {
                              match v0 {
                                &Value::BVal(_, b) => {
                                  None
                                },
                                &Value::ZVal(_, j) => {
                                  self.interp(
                                    ext,
                                    inst0,
                                    self.alloc(
                                      List::cons(
                                        PhantomData,
                                        self.alloc(
                                          Value::ZVal(
                                            PhantomData,
                                            self.add(
                                              i,
                                              j))),
                                        s0)),
                                    cond)
                                },
                              }
                            },
                          }
                        },
                      }
                    },
                  }
                },
                &Op::Sub(_) => {
                  match s {
                    &List::nil(_) => {
                      None
                    },
                    &List::cons(_, v, l) => {
                      match v {
                        &Value::BVal(_, b) => {
                          None
                        },
                        &Value::ZVal(_, i) => {
                          match l {
                            &List::nil(_) => {
                              None
                            },
                            &List::cons(_, v0, s0) => {
                              match v0 {
                                &Value::BVal(_, b) => {
                                  None
                                },
                                &Value::ZVal(_, j) => {
                                  self.interp(
                                    ext,
                                    inst0,
                                    self.alloc(
                                      List::cons(
                                        PhantomData,
                                        self.alloc(
                                          Value::ZVal(
                                            PhantomData,
                                            self.sub(
                                              i,
                                              j))),
                                        s0)),
                                    cond)
                                },
                              }
                            },
                          }
                        },
                      }
                    },
                  }
                },
                &Op::Mult(_) => {
                  match s {
                    &List::nil(_) => {
                      None
                    },
                    &List::cons(_, v, l) => {
                      match v {
                        &Value::BVal(_, b) => {
                          None
                        },
                        &Value::ZVal(_, i) => {
                          match l {
                            &List::nil(_) => {
                              None
                            },
                            &List::cons(_, v0, s0) => {
                              match v0 {
                                &Value::BVal(_, b) => {
                                  None
                                },
                                &Value::ZVal(_, j) => {
                                  self.interp(
                                    ext,
                                    inst0,
                                    self.alloc(
                                      List::cons(
                                        PhantomData,
                                        self.alloc(
                                          Value::ZVal(
                                            PhantomData,
                                            self.mul(
                                              i,
                                              j))),
                                        s0)),
                                    cond)
                                },
                              }
                            },
                          }
                        },
                      }
                    },
                  }
                },
                &Op::Lt(_) => {
                  match s {
                    &List::nil(_) => {
                      None
                    },
                    &List::cons(_, v, l) => {
                      match v {
                        &Value::BVal(_, b) => {
                          None
                        },
                        &Value::ZVal(_, i) => {
                          match l {
                            &List::nil(_) => {
                              None
                            },
                            &List::cons(_, v0, s0) => {
                              match v0 {
                                &Value::BVal(_, b) => {
                                  None
                                },
                                &Value::ZVal(_, j) => {
                                  self.interp(
                                    ext,
                                    inst0,
                                    self.alloc(
                                      List::cons(
                                        PhantomData,
                                        self.alloc(
                                          Value::BVal(
                                            PhantomData,
                                            self.ltb(
                                              i,
                                              j))),
                                        s0)),
                                    cond)
                                },
                              }
                            },
                          }
                        },
                      }
                    },
                  }
                },
                &Op::Le(_) => {
                  match s {
                    &List::nil(_) => {
                      None
                    },
                    &List::cons(_, v, l) => {
                      match v {
                        &Value::BVal(_, b) => {
                          None
                        },
                        &Value::ZVal(_, i) => {
                          match l {
                            &List::nil(_) => {
                              None
                            },
                            &List::cons(_, v0, s0) => {
                              match v0 {
                                &Value::BVal(_, b) => {
                                  None
                                },
                                &Value::ZVal(_, j) => {
                                  self.interp(
                                    ext,
                                    inst0,
                                    self.alloc(
                                      List::cons(
                                        PhantomData,
                                        self.alloc(
                                          Value::BVal(
                                            PhantomData,
                                            self.leb(
                                              i,
                                              j))),
                                        s0)),
                                    cond)
                                },
                              }
                            },
                          }
                        },
                      }
                    },
                  }
                },
                &Op::Equal(_) => {
                  match s {
                    &List::nil(_) => {
                      None
                    },
                    &List::cons(_, v, l) => {
                      match v {
                        &Value::BVal(_, b) => {
                          None
                        },
                        &Value::ZVal(_, i) => {
                          match l {
                            &List::nil(_) => {
                              None
                            },
                            &List::cons(_, v0, s0) => {
                              match v0 {
                                &Value::BVal(_, b) => {
                                  None
                                },
                                &Value::ZVal(_, j) => {
                                  self.interp(
                                    ext,
                                    inst0,
                                    self.alloc(
                                      List::cons(
                                        PhantomData,
                                        self.alloc(
                                          Value::BVal(
                                            PhantomData,
                                            self.eqb(
                                              i,
                                              j))),
                                        s0)),
                                    cond)
                                },
                              }
                            },
                          }
                        },
                      }
                    },
                  }
                },
              }
            },
            false => {
              self.interp(
                ext,
                inst0,
                s,
                cond)
            },
          }
        },
      }
    },
  }
}
fn interp__curried(&'a self) -> &'a dyn Fn(Ext_map<'a>) -> &'a dyn Fn(&'a List<'a, &'a Instruction<'a>>) -> &'a dyn Fn(&'a List<'a, &'a Value<'a>>) -> &'a dyn Fn(i64) -> Option<&'a List<'a, &'a Value<'a>>> {
  self.closure(move |ext| {
    self.closure(move |insts| {
      self.closure(move |s| {
        self.closure(move |cond| {
          self.interp(
            ext,
            insts,
            s,
            cond)
        })
      })
    })
  })
}

fn receive(&'a self, chain: &'a Chain<'a>, ctx: &'a ContractCallContext<'a>, s: Storage<'a>, msg: Option<Msg<'a>>) -> Option<__pair<Storage<'a>, &'a List<'a, ActionBody<'a>>>> {
  match msg {
    Some(m) => {
      __pair_elim!(
        insts, ext, {
          match self.interp(
                  ext,
                  insts,
                  self.alloc(
                    List::nil(
                      PhantomData)),
                  0) {
            Some(v) => {
              Some(
                __mk_pair(
                  v,
                  self.alloc(
                    List::nil(
                      PhantomData))))
            },
            None => {
              None
            },
          }
        },
        m)
    },
    None => {
      None
    },
  }
}
fn receive__curried(&'a self) -> &'a dyn Fn(&'a Chain<'a>) -> &'a dyn Fn(&'a ContractCallContext<'a>) -> &'a dyn Fn(Storage<'a>) -> &'a dyn Fn(Option<Msg<'a>>) -> Option<__pair<Storage<'a>, &'a List<'a, ActionBody<'a>>>> {
  self.closure(move |chain| {
    self.closure(move |ctx| {
      self.closure(move |s| {
        self.closure(move |msg| {
          self.receive(
            chain,
            ctx,
            s,
            msg)
        })
      })
    })
  })
}
}

#[init(contract = "interpreter", payable, enable_logger, low_level)]
fn contract_init<StateError: Default>(
    ctx: &impl HasInitContext<()>,
    amount: concordium_std::Amount,
    logger: &mut impl HasLogger,
    state: &mut impl HasContractState<StateError>
) -> Result<(), InitError> {
    let prg = Program::new();
    let params =
        match <_>::concert_deserial(&mut ctx.parameter_cursor(), &prg.__alloc) {
            Ok(p) => p,
            Err(_) => return Err(InitError::DeserialParams)
        };
    let cchain =
        Chain::build_chain(
            PhantomData,
            0, // No chain height
            ctx.metadata().slot_time().timestamp_millis(),
            0 // No finalized height
        );
    let cctx =
        ContractCallContext::build_ctx(
            PhantomData,
            Address::Account(ctx.init_origin()),
            Address::Contract(ContractAddress { index: 0, subindex: 0 }),
            amount.micro_gtu as i64,
            amount.micro_gtu as i64);
    let res = prg.init(&cchain, &cctx, params);
    match res {
        Option::Some(init_state) => {
            match init_state.concert_serial(state) {
                Ok(_) => Ok(()),
                Err(_) => Err(InitError::SerialParams)
            }
        }
        Option::None => Err(InitError::Error)
    }
}

fn convert_actions<A: HasActions>(acts: &List<ActionBody>) -> Result<A, ReceiveError> {
  match acts {
    &List::nil(_) => Ok(A::accept()),
    &List::cons(_, hd, tl) => {
      let cact =
        if let ActionBody::Transfer(Address::Account(acc), amount) = hd {
          let amount = convert::TryInto::try_into(amount).map_err(|_| ReceiveError::ConvertActions)?;
          A::simple_transfer(&acc, concordium_std::Amount::from_micro_gtu(amount))
        } else {
          return Err(ReceiveError::ConvertActions) // Cannot handle call to contract through ConCert, use Concordium functions instead
        };
      Ok(cact.and_then(convert_actions(tl)?))
    }
  }
}

#[receive(contract = "interpreter", name = "receive", payable, enable_logger, low_level)]
fn contract_receive<A: HasActions, StateError: Default>(
    ctx: &impl HasReceiveContext<()>,
    amount: concordium_std::Amount,
    logger: &mut impl HasLogger,
    state: &mut impl HasContractState<StateError>,
) -> Result<A, ReceiveError> {
    let prg = Program::new();
    let msg =
        match <_>::concert_deserial(&mut ctx.parameter_cursor(), &prg.__alloc) {
            Ok(m) => m,
            Err(_) => return Err(ReceiveError::DeserialMsg)
        };
    let old_state =
        match <_>::concert_deserial(state, &prg.__alloc) {
            Ok(s) => s,
            Err(_) => return Err(ReceiveError::DeserialOldState)
        };
    let cchain =
        Chain::build_chain(
            PhantomData,
            0, // No chain height
            ctx.metadata().slot_time().timestamp_millis(),
            0 // No finalized height
        );
    let cctx =
        ContractCallContext::build_ctx(
            PhantomData,
            ctx.sender(),
            Address::Contract(ctx.self_address()),
            ctx.self_balance().micro_gtu as i64,
            amount.micro_gtu as i64);
    let res = prg.receive(&cchain, &cctx, old_state, msg);
    match res {
        Option::Some((new_state, acts)) => {
            state.truncate(0);
            match new_state.concert_serial(state) {
                Ok(_) => convert_actions(acts),
                Err(_) => Err(ReceiveError::SerialNewState)
            }
        }
        Option::None => Err(ReceiveError::Error)
    }
}
