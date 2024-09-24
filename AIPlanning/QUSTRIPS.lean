import AIPlanning.STRIPS

namespace AIPlanning.QUSTRIPS

class BeliefLevel (α: Type) where
  fromInt: Int → Option α
  toInt: α → Int

namespace BeliefLevel

instance [BeliefLevel α] : BEq α where
  beq a b := BeliefLevel.toInt a == BeliefLevel.toInt b

instance [BeliefLevel α] : LT α where
  lt a b := BeliefLevel.toInt a < BeliefLevel.toInt b

instance [BeliefLevel α] : LE α where
  le a b := a == b || a < b

instance [BeliefLevel α] {x1 x2: α}: Decidable (x1 ≤ x2) := by
  rewrite [LE.le, instLE]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  apply inferInstance

instance [BeliefLevel α] (b₁ b₂ : α): Decidable (b₁ < b₂) := by
  rewrite [LT.lt, instLT]
  simp only [gt_iff_lt]
  apply inferInstance

instance [BeliefLevel α] : Min α := minOfLe

theorem unique_integer_repr (α : Type) [BeliefLevel α] : ∀ b₁ b₂ : α, b₁ != b₂ ↔ BeliefLevel.toInt b₁ != BeliefLevel.toInt b₂ := by
  intro b₁ b₂
  exact (fun a b ↦ (Bool.coe_iff_coe a b).mpr) (b₁ != b₂) (toInt b₁ != toInt b₂) rfl

def inverse? {α : Type} [BeliefLevel α] (b: α): Option α :=
  fromInt (-1 * (toInt b))

end BeliefLevel


/-Properties of BeliefLevels-/
class LawfulBeliefLevel (α : Type) [BeliefLevel α]  where
  agnostic_exists : ∃ (x : α), BeliefLevel.fromInt 0 = some x
  conversion_sound₁ : ∀ (b : α), BeliefLevel.fromInt (BeliefLevel.toInt b) = some b
  conversion_sound₂ : ∀ (i: Int), ∀ (b: α), BeliefLevel.fromInt i = some (b: α) → BeliefLevel.toInt b = i
  inverse_exists : ∀ (b : α), ∃ (b₂ : α), BeliefLevel.inverse? b = some b₂


namespace BeliefLevel
def Agnostic {α: Type} [BeliefLevel α] [LawfulBeliefLevel α]: α :=
  (BeliefLevel.fromInt 0).get (by
    have H := @LawfulBeliefLevel.agnostic_exists α
    exact Option.isSome_iff_exists.mpr H
  )

def inverse {α : Type} [BeliefLevel α] [LawfulBeliefLevel α] (b: α): α :=
  (BeliefLevel.inverse? b).get (by
    have H := @LawfulBeliefLevel.inverse_exists α
    exact Option.isSome_iff_exists.mpr (H b)
  )
end BeliefLevel

namespace LawfulBeliefLevel

theorem agnostic_zero_1 {α : Type} [BeliefLevel α] [LawfulBeliefLevel α]: BeliefLevel.fromInt 0 = some (BeliefLevel.Agnostic : α) := by
  unfold BeliefLevel.Agnostic
  exact Option.eq_some_of_isSome BeliefLevel.Agnostic.proof_1

theorem agnostic_zero_2 {α : Type} [BeliefLevel α] [LawfulBeliefLevel α] : BeliefLevel.toInt (BeliefLevel.Agnostic : α) = 0 := by
  let x: α := BeliefLevel.Agnostic
  rw [BeliefLevel.Agnostic.eq_def]
  have H0 : ∀ (i: Int), ∀ (b: α), BeliefLevel.fromInt i = some (b: α) → BeliefLevel.toInt b = i := conversion_sound₂
  have H1: BeliefLevel.fromInt 0 = some x → BeliefLevel.toInt x = 0 := H0 0 x
  have H2 : BeliefLevel.fromInt 0 = some x := agnostic_zero_1
  exact H1 H2


theorem agnostic_inverse_self (α : Type) [BeliefLevel α] [LawfulBeliefLevel α] : (BeliefLevel.Agnostic: α) = BeliefLevel.inverse (BeliefLevel.Agnostic: α) := by
  rw [BeliefLevel.inverse.eq_def]
  unfold BeliefLevel.inverse?
  have H0 : BeliefLevel.toInt (BeliefLevel.Agnostic : α) = 0 := agnostic_zero_2
  have H1 : -1 * BeliefLevel.toInt (BeliefLevel.Agnostic: α) = 0 := by
    rw [H0]
    rfl
  have H2 : BeliefLevel.fromInt (-1 * BeliefLevel.toInt (BeliefLevel.Agnostic : α)) = some (BeliefLevel.Agnostic: α) := by
    rw [H1]
    apply agnostic_zero_1
  exact Eq.symm (Option.get_of_mem (BeliefLevel.inverse.proof_1 BeliefLevel.Agnostic) H2)

end LawfulBeliefLevel

inductive BL5 where
  | CERTAINLY_NOT
  | EVIDENTLY_NOT
  | AGNOSTIC
  | EVIDENTLY
  | CERTAINLY
deriving DecidableEq, Hashable, Repr

instance : BeliefLevel BL5 where
  fromInt i := match i with
    | -2 => some .CERTAINLY_NOT
    | -1 => some .EVIDENTLY_NOT
    | 0 =>  some .AGNOSTIC
    | 1 =>  some .EVIDENTLY
    | 2 =>  some .CERTAINLY
    | _ =>  none
  toInt b := match b with
    | .CERTAINLY_NOT => -2
    | .EVIDENTLY_NOT => -1
    | .AGNOSTIC => 0
    | .EVIDENTLY => 1
    | .CERTAINLY => 2


instance : LawfulBeliefLevel BL5 where
  agnostic_exists := by
    existsi .AGNOSTIC
    rfl
  inverse_exists := by
    intro b
    cases b
    case CERTAINLY_NOT => existsi .CERTAINLY; rfl
    case EVIDENTLY_NOT => existsi .EVIDENTLY; rfl
    case AGNOSTIC => existsi .AGNOSTIC; rfl
    case EVIDENTLY => existsi .EVIDENTLY_NOT; rfl
    case CERTAINLY => existsi .CERTAINLY_NOT; rfl
  conversion_sound₁ := by
    intro b
    cases b
    all_goals rfl
  conversion_sound₂ := by
    intro i
    intro b
    intro H
    unfold BeliefLevel.fromInt at H
    unfold BeliefLevel.toInt
    unfold instBeliefLevelBL5 at *
    simp only at H
    simp only
    cases b
    case CERTAINLY_NOT =>
      simp
      have H2: i = -2 ∨ i = -1 ∨ i = 0 ∨ i = 1 ∨ i = 2 ∨ (i != -2 ∧ i != -1 ∧ i != 0 ∧ i != 1 ∧ i != 2) := by sorry
      cases' H2 with H3 H2
      omega
      repeat (
        cases' H2 with H3 H2
        rw [H3] at H
        contradiction
      )
      sorry
    sorry
    sorry
    sorry
    sorry





structure BeliefProp (α: Type) [BeliefLevel α]  extends STRIPS.SProp where
  level: α
deriving BEq, DecidableEq, Hashable, Repr

def ground [BeliefLevel α] (b: BeliefProp α): STRIPS.SProp :=
  b.toSProp

def strength [BeliefLevel α] (b: BeliefProp α): α :=
  b.level

abbrev BeliefSet α [BeliefLevel α] [BEq α] [Hashable α] := Std.HashSet (BeliefProp α)

#check BeliefSet BL5

structure BeliefOperator (α: Type) [BeliefLevel α] [BEq α] [Hashable α] where
  name: String
  preconditions: BeliefSet α
  add_p: List (BeliefSet α × BeliefSet α)
  add_n: List (BeliefSet α × BeliefSet α)
  cost: Nat

instance [BeliefLevel α] [BEq α] [Hashable α] : BEq (BeliefOperator α) where
  beq o1 o2 :=
    o1.name == o2.name &&
    o1.preconditions == o2.preconditions &&
    o1.add_p == o2.add_p &&
    o1.add_n == o2.add_n &&
    o1.cost == o2.cost


-- def Satisfies [BeliefLevel α] [LawfulBeliefLevel α] [BEq α] [Hashable α] (s: BeliefSet α) (requirements: STRIPS.PropSet) : Prop :=
--   ∀ p ∈ requirements, ∃ si ∈ s, ground si = p ∧ strength si > BeliefLevel.agnostic


-- set_option pp.notation false

-- instance [BeliefLevel α] [LawfulBeliefLevel α] [BEq α] [Hashable α] (s: BeliefSet α) (requirements: STRIPS.PropSet) : Decidable (Satisfies s req) := by
--   unfold Satisfies
--   cases' req with innerHashMap
--   cases' innerHashMap with innerDHashMap
--   cases' innerDHashMap with innerDHashMapRaw
--   cases' innerDHashMapRaw with size buckets
--   cases' buckets with bucketList


-- Alternative: Present this definition in a mathematical
-- way and then show it's a DecidableRel
/- Ensure that all the requirements are satisfied at a belief level greater than agnostic -/
def satisfies [BeliefLevel α] [LawfulBeliefLevel α] [BEq α] [Hashable α] (s: BeliefSet α) (requirements: STRIPS.PropSet): Bool :=
  Std.HashSet.fold
  (fun result => fun p =>
    result && Std.HashSet.fold
              (fun result2 => fun b =>
                result2 || (ground b == p && (strength b > BeliefLevel.Agnostic)))
              false
              s)
  true

  requirements

#check (inferInstance: Min BL5)

def wlp [BeliefLevel α] [BEq α] [Hashable α] (s: BeliefSet α) (conditions: STRIPS.PropSet): α :=
  (List.minimum? (List.filterMap (fun si => if conditions.contains (ground si) then some (strength si) else none) s.toList)).get
  (by sorry)


end AIPlanning.QUSTRIPS
