import Std.Data.HashSet
import AIPlanning.STRIPS
namespace AIPlanning
open STRIPS

namespace Tests.STRIPS

namespace Problem1

def initialState : PropSet := Std.HashSet.ofList [
  "at-agent-A",
  "CONNECTED-A-B",
  "CONNECTED-A-C",
  "CONNECTED-B-C"
]

def goalCondition : PropSet := [
  "at-agent-C"
]

def moveAB := Operator.mk "move-A-B"
  ["at-agent-A", "CONNECTED-A-B"]
  ["at-agent-B"]
  ["at-agent-A"]
  1

def moveAC := Operator.mk "move-A-C"
  ["at-agent-A", "CONNECTED-A-C"]
  ["at-agent-C"]
  ["at-agent-A"]
  1

def moveBC := Operator.mk "move-B-C"
  ["at-agent-B", "CONNECTED-B-C"]
  ["at-agent-C"]
  ["at-agent-B"]
  1

def operators : List Operator := [
  moveAB, moveAC, moveBC
]

def problem : Problem := Problem.mk
  operators
  initialState
  goalCondition

structure PlanSummary where
  actions: List String -- Only the name
  cost: Nat
deriving Repr, BEq

def PlanSummary.fromPlan (p: Plan) :=
  have ⟨actions, cost⟩ := p.foldl (fun ⟨as, c⟩ => fun a => (as ++ [a.name], c + a.cost)) ([], 0)
  PlanSummary.mk actions cost

def solutions := (bfs_plan problem).map PlanSummary.fromPlan

#guard solutions.length = 2
#guard solutions.contains (PlanSummary.mk ["move-A-C"] 1)
#guard solutions.contains (PlanSummary.mk ["move-A-B", "move-B-C"] 2)

end Problem1

end AIPlanning.Tests.STRIPS
