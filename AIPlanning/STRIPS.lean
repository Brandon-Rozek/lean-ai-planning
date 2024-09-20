import Std.Data.HashSet
import Mathlib.Data.List.Sort
import AIPlanning.HashSet

namespace AIPlanning.STRIPS
structure SProp where
  name : String
deriving BEq, DecidableEq, Hashable, Repr

instance : Coe String SProp where
  coe s := SProp.mk s

instance : LawfulBEq SProp where
  eq_of_beq {a b} H := by
    cases a; cases b
    next name1 name2 =>
      simp only [SProp.mk.injEq]
      have H2 : (name1 == name2) = true := H
      apply instLawfulBEqString.eq_of_beq H2

  rfl := by
    intro a
    cases a
    next name =>
      exact beq_self_eq_true' name

abbrev PropSet := Std.HashSet SProp

instance : Coe (List String) PropSet where
  coe s := Std.HashSet.ofList s

structure Operator where
  name: String
  preconditions: PropSet
  additions: PropSet
  deletions: PropSet
  cost: Nat
deriving Repr

instance : BEq Operator where
  beq o1 o2 :=
    o1.name == o2.name &&
    o1.preconditions == o2.preconditions &&
    o1.additions == o2.additions &&
    o1.deletions == o2.deletions &&
    o1.cost == o2.cost

def withinOperators (o: Operator) (os: List Operator) : Bool :=
  match os with
  | [] => false
  | (oi::os) => if oi == o then true else withinOperators o os

structure Problem where
  operators: List Operator
  initialState: PropSet
  goalCondition: PropSet
deriving Repr

def satisfies(s requirements: PropSet): Bool :=
  requirements ⊆ s

def apply (state: PropSet) (o: Operator) : PropSet :=
  (state \ o.deletions) ∪ o.additions

abbrev Plan := List Operator

private def is_valid_helper (operators: List Operator) (goalCondition: PropSet) (currentState: PropSet) (plan: Plan) : Bool :=
  match plan with
  | [] => satisfies currentState goalCondition
  | (a::as) =>
    have validOperator := withinOperators a operators
    have satisfiesPre := satisfies currentState a.preconditions
    if validOperator && satisfiesPre then
      have nextState := apply currentState a
      is_valid_helper operators goalCondition nextState as
    else
      false

def is_valid (Pi: Problem) (plan: Plan): Bool :=
  is_valid_helper Pi.operators Pi.goalCondition Pi.initialState plan

def has_seen (state: PropSet) (seen: List PropSet) : Bool :=
  match seen with
  | [] => false
  | (s::ss) =>
    if state == s then true else has_seen state ss

-- Assumes that queue is sorted in priority order
private partial def bfs_plan_helper (queue: List (Nat × PropSet × Plan)) (seen: List PropSet) (operators: List Operator) (goalCondition: PropSet) (plans: List Plan): List Plan :=
  match queue with
  | [] => plans
  | (cost, currentState, currentPlan) :: restQueue =>
    if satisfies currentState goalCondition then
      have newPlans := (currentPlan :: plans)
      bfs_plan_helper restQueue seen operators goalCondition newPlans
    else
      have nextSeen := currentState :: seen
      -- Apply every applicable operator and
      -- collect the next tuples
      have nextItems := operators.filterMap (fun o =>
        if satisfies currentState o.preconditions then
          have nextState := apply currentState o
          -- Prune cycles
          if not (has_seen nextState nextSeen) then
            have nextCost: Nat := cost + o.cost
            have nextPlan := currentPlan ++ [o]
            some (nextCost, nextState, nextPlan)
          else
            none
        else
          none
      )
      -- Remove duplicate states within nextItems
      have nextItems := nextItems.pwFilter (fun s1 => fun s2 => s1.2.1 != s2.2.1)
      have nextQueue := (restQueue ++ nextItems).insertionSort (fun x => fun y => x.1 ≤ y.1)
      bfs_plan_helper nextQueue nextSeen operators goalCondition plans


def bfs_plan (problem: Problem): List Plan :=
  bfs_plan_helper [(0, problem.initialState, [])]
                  []
                  problem.operators
                  problem.goalCondition
                  []

end AIPlanning.STRIPS
