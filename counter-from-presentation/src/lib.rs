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

#[derive(Debug, PartialEq, Eq, Reject)]
enum ReceiveError {
    DeserialMsg,
    DeserialOldState,
    SerialNewState,
    ConvertActions, // Cannot convert ConCert actions to Concordium actions
    Error
}

#[derive(Clone, ConCertSerial, ConCertDeserial, PartialEq)]
pub enum Chain<'a> {
  build_chain(PhantomData<&'a ()>, u64, u64, u64)
}

#[derive(Clone, ConCertSerial, ConCertDeserial, PartialEq)]
pub enum List<'a, A> {
  nil(PhantomData<&'a A>),
  cons(PhantomData<&'a A>, A, &'a List<'a, A>)
}

type Address<'a> = concordium_std::Address;

type Amount<'a> = i64;

#[derive(Clone, ConCertSerial, ConCertDeserial, PartialEq)]
pub enum ContractCallContext<'a> {
  build_ctx(PhantomData<&'a ()>, Address<'a>, Address<'a>, Amount<'a>, Amount<'a>)
}

type State<'a> = i64;

#[derive(Clone, ConCertSerial, ConCertDeserial, PartialEq)]
pub enum Msg<'a> {
  Inc(PhantomData<&'a ()>, i64),
  Dec(PhantomData<&'a ()>, i64)
}

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

fn counter_init(&'a self, chain: &'a Chain<'a>, ctx: &'a ContractCallContext<'a>, init_value: i64) -> Option<State<'a>> {
  Some(
    0)
}
fn counter_init__curried(&'a self) -> &'a dyn Fn(&'a Chain<'a>) -> &'a dyn Fn(&'a ContractCallContext<'a>) -> &'a dyn Fn(i64) -> Option<State<'a>> {
  self.closure(move |chain| {
    self.closure(move |ctx| {
      self.closure(move |init_value| {
        self.counter_init(
          chain,
          ctx,
          init_value)
      })
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

fn counter_receive(&'a self, state: State<'a>, msg: &'a Msg<'a>) -> Option<__pair<State<'a>, &'a List<'a, ActionBody<'a>>>> {
  match msg {
    &Msg::Inc(_, i) => {
      match self.ltb(
              0,
              i) {
        true => {
          Some(
            __mk_pair(
              self.add(
                state,
                i),
              self.alloc(
                List::nil(
                  PhantomData))))
        },
        false => {
          None
        },
      }
    },
    &Msg::Dec(_, i) => {
      match self.ltb(
              0,
              i) {
        true => {
          Some(
            __mk_pair(
              self.sub(
                state,
                i),
              self.alloc(
                List::nil(
                  PhantomData))))
        },
        false => {
          None
        },
      }
    },
  }
}
fn counter_receive__curried(&'a self) -> &'a dyn Fn(State<'a>) -> &'a dyn Fn(&'a Msg<'a>) -> Option<__pair<State<'a>, &'a List<'a, ActionBody<'a>>>> {
  self.closure(move |state| {
    self.closure(move |msg| {
      self.counter_receive(
        state,
        msg)
    })
  })
}

fn counter_receive_wrapper(&'a self, chain: &'a Chain<'a>, ctx: &'a ContractCallContext<'a>, state: State<'a>, msg: Option<&'a Msg<'a>>) -> Option<__pair<State<'a>, &'a List<'a, ActionBody<'a>>>> {
  match msg {
    Some(m) => {
      self.counter_receive(
        state,
        m)
    },
    None => {
      None
    },
  }
}
fn counter_receive_wrapper__curried(&'a self) -> &'a dyn Fn(&'a Chain<'a>) -> &'a dyn Fn(&'a ContractCallContext<'a>) -> &'a dyn Fn(State<'a>) -> &'a dyn Fn(Option<&'a Msg<'a>>) -> Option<__pair<State<'a>, &'a List<'a, ActionBody<'a>>>> {
  self.closure(move |chain| {
    self.closure(move |ctx| {
      self.closure(move |state| {
        self.closure(move |msg| {
          self.counter_receive_wrapper(
            chain,
            ctx,
            state,
            msg)
        })
      })
    })
  })
}
}

#[init(contract = "counter", payable, enable_logger, low_level)]
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
    let res = prg.counter_init(&cchain, &cctx, params);
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

#[receive(contract = "counter", name = "counter_receive_wrapper", payable, enable_logger, low_level)]
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
    let res = prg.counter_receive_wrapper(&cchain, &cctx, old_state, msg);
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
