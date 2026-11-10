module

public import ArtinMatthews.GiantSignedTraceChronology
public import ArtinMatthews.GiantSignedTraceOfChronology
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Pack the actual chronology and its chosen pattern and birth counts.
Consing the first ordered move onto its original suffix is exact. -/

namespace ArtinMatthews
noncomputable section

universe u
variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}

abbrev GiantSignedPackedChronology (PS : S → Finset ℕ) (PB : B → Finset ℕ)
    (ell : ℕ) {k n : ℕ} (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k)) :=
  Σ pattern : ((i : Fin n) → patterns i), Σ batch : Fin (n+1) → B → ℕ,
    GiantSignedChronologicalChoices PS PB ell (fun i => C i (pattern i).val) batch

def giantSignedTraceChronology_pack {patterns : Fin n → Finset I} {C : Fin n → I → B → Finset (Fin k)}
    {s : GiantSignedState PS PB (k+ell)} (z : GiantSignedTraceChronology s patterns C) :
    GiantSignedPackedChronology PS PB ell patterns C := ⟨z.pattern,z.batch,z.history⟩

def giantSignedPackedChronology_prepend
    (patterns : Fin (n+1) → Finset I) (C : Fin (n+1) → I → B → Finset (Fin k))
    (s : GiantSignedState PS PB (k+ell)) (r : GiantSignedGhostMemoryMoves s.2.2)
    (e : Σ p : patterns 0, GiantSignedRawEdgeMove PS PB ell (C 0 p.val)
      (giantSignedGhostMemoryMoveTarget s.2.2 r))
    (tail : GiantSignedPackedChronology PS PB ell (fun i => patterns i.succ) (fun i => C i.succ)) :
    GiantSignedPackedChronology PS PB ell patterns C := by
  let state : Fin (n+2) → GiantSignedState PS PB (k+ell) := Fin.cons s tail.2.2.state
  let batch : Fin (n+2) → B → ℕ := Fin.cons (fun g => (r g).2.1) tail.2.1
  let pattern : (i : Fin (n+1)) → patterns i := Fin.cons e.1 tail.1
  let deleted : (i : Fin (n+2)) → (g : B) → Finset (Fin ((state i).2.2.1 g)) :=
    Fin.cons (fun g => (r g).1) tail.2.2.deleted
  let born : (i : Fin (n+2)) → (g : B) → Fin (batch i g) → PB g :=
    Fin.cons (fun g => (r g).2.2) tail.2.2.born
  have he : (giantSignedFixedGhostTarget s.2.2 (fun g => (r g).2.1) (fun g => (r g).1)
      (fun g => (r g).2.2)).1 = (giantSignedGhostMemoryMoveTarget s.2.2 r).1 :=
    congrArg (fun m : GiantSignedGhostMemoryMoves s.2.2 => (giantSignedGhostMemoryMoveTarget s.2.2 m).1)
      (giantSignedFixedGhostMove_of_move s.2.2 r)
  exact ⟨pattern,batch,{
    state := state
    deleted := deleted
    born := born
    sourceSmallPermutation := Fin.cons e.2.sourceSmallPermutation tail.2.2.sourceSmallPermutation
    targetSmallPermutation := Fin.cons e.2.targetSmallPermutation tail.2.2.targetSmallPermutation
    sourceBigPermutation := Fin.cons e.2.sourceBigPermutation tail.2.2.sourceBigPermutation
    targetBigPermutation := Fin.cons e.2.targetBigPermutation tail.2.2.targetBigPermutation
    auxiliary := Fin.cons e.2.auxiliary tail.2.2.auxiliary
    edge := Fin.cons (he.symm ▸ e.2.choice) tail.2.2.edge }⟩

theorem giantSignedPackedChronology_prepend_tail
    (patterns : Fin (n+1) → Finset I) (C : Fin (n+1) → I → B → Finset (Fin k))
    (p : (i : Fin (n+1)) → patterns i) (batch : Fin (n+2) → B → ℕ)
    (h : GiantSignedChronologicalChoices PS PB ell (fun i => C i (p i).val) batch) :
    giantSignedPackedChronology_prepend patterns C (h.state 0)
      (giantSignedFixedGhostMove (h.state 0).2.2 (batch 0) (h.deleted 0) (h.born 0))
      ⟨p 0,giantSignedChronologicalRawMove h 0⟩
      ⟨fun i => p i.succ, fun i => batch i.succ, giantSignedChronologicalTail h⟩ = ⟨p,batch,h⟩ := by
  induction p using Fin.consCases
  induction batch using Fin.consCases
  rcases h with ⟨state,deleted,born,πS,τS,πB,τB,aux,edge⟩
  induction state using Fin.consCases
  induction deleted using Fin.consCases
  induction born using Fin.consCases
  induction πS using Fin.consCases
  induction τS using Fin.consCases
  induction πB using Fin.consCases
  induction τB using Fin.consCases
  induction aux using Fin.consCases
  induction edge using Fin.consCases
  rfl

end
end ArtinMatthews
