import Std.Data.HashSet

namespace Std

def subset [BEq α] [Hashable α] (s t : HashSet α) : Bool :=
  s.fold (fun r => fun si => r && (t.contains si)) true

instance [BEq α] [Hashable α] : HasSubset (HashSet α) :=
  ⟨fun s t => subset s t⟩

instance [BEq α] [Hashable α] : DecidableRel (Subset : HashSet α → Std.HashSet α → Prop) := by
  unfold DecidableRel
  intro s t
  rewrite [Subset, instHasSubsetHashSet_aIPlanning]
  simp only
  exact (subset s t).decEq true

def union [BEq α] [Hashable α] (s t : HashSet α) : HashSet α :=
  t.fold (fun newC => fun ti => newC.insert ti) s

instance [BEq α] [Hashable α] : Union (HashSet α) :=
  ⟨fun s t => union s t⟩

def inter [BEq α] [Hashable α] (s t : HashSet α) : HashSet α :=
  s.fold (fun newC => fun si => if (t.contains si) then newC.insert si else newC) (Std.HashSet.empty s.size)

instance [BEq α] [Hashable α] : Inter (HashSet α) :=
  ⟨fun s t => inter s t⟩

def sdiff [BEq α] [Hashable α] (s t : HashSet α) : HashSet α :=
  s.filter (fun si => ¬(si ∈ t))

instance [BEq α] [Hashable α] : SDiff (HashSet α) :=
  ⟨fun s t => sdiff s t⟩

instance [BEq α] [Hashable α] : BEq (HashSet α) where
  beq s t := if s.size != t.size then
    false
  else
    s.fold (fun result => fun si => result && (t.contains si)) true


end Std
