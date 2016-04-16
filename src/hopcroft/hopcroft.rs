use std::cmp::{Ord, Ordering};
use std::vec::Vec;
use hopcroft::partition::{Partition, Set};

pub enum StateT {}
enum TransitionT {}

type State = usize;

pub struct Transition<L> {
  lbl : L,
  src : State,
  dst : State,
}

pub struct Automaton<L> {
  /// Number of states
  states : usize,
  /// List of unique transitions between states
  transitions : Box<[Transition<L>]>,
}

pub trait Hopcroft<T> {

/// Associate the equivalence classes of the states of an automaton
fn reduce (a : &mut Automaton<T>) -> Partition<StateT>;

}

struct Environment {
  /// Current partition of the states
  state_partition : Partition<StateT>,
  /// Current partition of the transitions
  transition_partition : Partition<TransitionT>,
  /// Associate to each transition its source
  transition_source : Box<[usize]>,
  /// Associate to each state the list of transitions that ends in it
  state_pred_trans : Box<[Vec<usize>]>,
  /// Partitions waiting to be processed
  partition_todo : Vec<Set<TransitionT>>,
}

/// Associate the list of transitions ending in a given state
fn reverse<T>(automaton : &Automaton<T>) -> Box<[Vec<usize>]> {
  let mut ans = Vec::with_capacity(automaton.states);
  for _ in 0..automaton.states {
    ans.push(Vec::new());
  }
  let mut ans = ans.into_boxed_slice();
  let mut i : usize = 0;
  for trans in automaton.transitions.into_iter() {
    ans[trans.dst].push(i);
    i = i + 1;
  }
  ans
}

fn init<T : Ord>(automaton : &mut Automaton<T>) -> Environment {
  // Sort transitions according to their label
  automaton.transitions.sort_by(|x, y| { Ord::cmp(&(x.lbl), &(y.lbl)) });
  // Initialize the environment
  let len = automaton.transitions.len();
  let st_part = Partition::new(automaton.states);
  let mut sp_part = Partition::new(len);
  let mut trans_src = Vec::with_capacity(len);
  // Set the source of the transitions
  for i in 0..len { trans_src.push(automaton.transitions[i].src) }
  let trans_src = trans_src.into_boxed_slice();
  // Split splitters according to their label
  if len > 0 {
    let mut label0 = &(automaton.transitions[0].lbl);
    // pt is initial, full partition
    let pt = sp_part.partition(0);
    for i in 0..len {
      // Each time the label changes, we split
      let label = &(automaton.transitions[i].lbl);
      let _ = match Ord::cmp(label, label0) {
        Ordering::Equal => {}
        _ => {
          let _ = sp_part.split(pt);
          label0 = label;
        }
      };
      sp_part.mark(i);
    }
    let _ = sp_part.split(pt);
  }
  // Push every splitter in the todo stack
  let mut todo = Vec::with_capacity(sp_part.len());
  for partition in sp_part.into_iter() {
    todo.push(partition);
  }
  Environment {
    state_partition : st_part,
    transition_partition : sp_part,
    transition_source : trans_src,
    state_pred_trans : reverse(automaton),
    partition_todo : todo,
  }
}

fn split_partition(s : Set<StateT>, env : &mut Environment, splitter_touched : &mut Vec<Set<TransitionT>>) {
  assert!(splitter_touched.is_empty());
  let r = match env.state_partition.split(s) {
    None => { return; }
    Some (r) => { r }
  };
  let r = if env.state_partition.size(r) < env.state_partition.size(s) { r } else { s };
  for state in env.state_partition.class(r).into_iter() {
    let ref preds = env.state_pred_trans[state];
    for trans in preds {
      let pt = env.transition_partition.partition(*trans);
      if !env.transition_partition.is_marked(pt) {
        splitter_touched.push(pt);
      };
      env.transition_partition.mark(*trans);
    }
  }
  for pt in splitter_touched.drain(..) {
    match env.transition_partition.split(pt) {
      None => (),
      Some (npt) => { env.partition_todo.push(npt) },
    }
  }
}

fn reduce_loop(env : &mut Environment, state_touched : &mut Vec<Set<StateT>>, splitter_touched : &mut Vec<Set<TransitionT>>) {
  assert!(state_touched.is_empty());
  assert!(splitter_touched.is_empty());
  match env.partition_todo.pop() {
    None => (),
    Some (pt) => {
      for trans in env.transition_partition.class(pt).into_iter() {
        let previous = env.transition_source[trans];
        let equiv = env.state_partition.partition(previous);
        if !env.state_partition.is_marked(equiv) {
          state_touched.push(equiv);
        }
        env.state_partition.mark(previous);
      }
      for state in state_touched.drain(..) {
        split_partition(state, env, splitter_touched);
      }
      reduce_loop(env, state_touched, splitter_touched);
    }
  }
}

impl<T> Hopcroft<T> for T where T : Ord {

fn reduce (automaton : &mut Automaton<T>) -> Partition<StateT> {
  let mut env = init(automaton);
  let mut state_touched = Vec::new();
  let mut splitter_touched = Vec::new();
  reduce_loop(&mut env, &mut state_touched, &mut splitter_touched);
  env.state_partition
}

}
