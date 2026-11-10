module

public import ArtinMatthews.GiantSignedTraceRows
public import ArtinMatthews.GiantSignedChronologicalChoices
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

/-! Read the actual ordered choices from the dependent word trace.
The batch sizes, patterns and four permutations come from its moves. -/
namespace ArtinMatthews
noncomputable section

universe u
variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}

structure GiantSignedTraceChronology (s : GiantSignedState PS PB (k+ell))
    (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k)) where
  pattern : (i : Fin n) → patterns i
  batch : Fin (n+1) → B → ℕ
  history : GiantSignedChronologicalChoices PS PB ell (fun i => C i (pattern i).val) batch
  first : history.state 0 = s

theorem giantSignedFixedGhostMove_of_move (m : GiantSignedMemory PB) (r : GiantSignedGhostMemoryMoves m) :
    giantSignedFixedGhostMove m (fun g => (r g).2.1) (fun g => (r g).1)
      (fun g => (r g).2.2) = r := by
  funext g
  change (⟨(r g).1, (r g).2.1, (r g).2.2⟩ : GiantSignedGhostMoves (giantSignedMemoryGroupEquiv PB m g)) = r g
  rcases r g with ⟨a,b,c⟩
  rfl

def giantSignedTraceChronology (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ) :
    (n : ℕ) → (patterns : Fin n → Finset I) → (C : Fin n → I → B → Finset (Fin k)) →
      (κ : Fin n → ℤ) → (visitQ : Fin (n+1) → ℝ) → (ζ : Fin n → ℝ) →
      (K : (i : Fin n) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell) →
      (η : (i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
        GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ) →
      (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedTrace (giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η) s →
      GiantSignedTraceChronology s patterns C
  | 0, _, _, _, _, _, _, _, s, t => by
      change (Σ _ : GiantSignedGhostMemoryMoves s.2.2, PUnit) at t
      exact {
        pattern := fun i => Fin.elim0 i
        batch := fun _ g => (t.1 g).2.1
        history := {
          state := fun _ => s
          deleted := fun _ g => (t.1 g).1
          born := fun _ g => (t.1 g).2.2
          sourceSmallPermutation := Fin.elim0
          targetSmallPermutation := Fin.elim0
          sourceBigPermutation := Fin.elim0
          targetBigPermutation := Fin.elim0
          auxiliary := fun i => Fin.elim0 i
          edge := fun i => Fin.elim0 i }
        first := rfl }
  | n+1, patterns, C, κ, visitQ, ζ, K, η, s, t => by
      let rest := giantSignedChronologicalTraceRows ν V q ρ θ n (fun i => patterns i.succ)
        (fun i => C i.succ) (fun i => κ i.succ) (fun i => visitQ i.succ) (fun i => ζ i.succ)
        (fun i => K i.succ) (fun i => η i.succ)
      let after (r : GiantSignedGhostMemoryMoves s.2.2) : GiantSignedState PS PB (k+ell) :=
        (s.1, s.2.1, giantSignedGhostMemoryMoveTarget s.2.2 r)
      let Moves (r : GiantSignedGhostMemoryMoves s.2.2) :=
        Σ v : patterns 0, GiantSignedRawEdgeMove PS PB ell (C 0 v.val) (after r).2.2
      let next (r : GiantSignedGhostMemoryMoves s.2.2) (e : Moves r) :=
        giantSignedRawEdgeTarget (κ 0) (after r) e.2
      change (Σ r : GiantSignedGhostMemoryMoves s.2.2, Σ e : Moves r,
        GiantSignedTrace rest (next r e)) at t
      let r := t.1
      let e := t.2.1
      let tail := giantSignedTraceChronology ν V q ρ θ n (fun i => patterns i.succ)
        (fun i => C i.succ) (fun i => κ i.succ) (fun i => visitQ i.succ) (fun i => ζ i.succ)
        (fun i => K i.succ) (fun i => η i.succ) (next r e) t.2.2
      let state : Fin (n+2) → GiantSignedState PS PB (k+ell) := Fin.cons s tail.history.state
      let batch : Fin (n+2) → B → ℕ := Fin.cons (fun g => (r g).2.1) tail.batch
      let pattern : (i : Fin (n+1)) → patterns i := Fin.cons e.1 tail.pattern
      let deleted : (i : Fin (n+2)) → (g : B) → Finset (Fin ((state i).2.2.1 g)) :=
        Fin.cons (fun g => (r g).1) tail.history.deleted
      let born : (i : Fin (n+2)) → (g : B) → Fin (batch i g) → PB g :=
        Fin.cons (fun g => (r g).2.2) tail.history.born
      have hhead : (giantSignedFixedGhostTarget s.2.2 (fun g => (r g).2.1)
          (fun g => (r g).1) (fun g => (r g).2.2)).1 = (after r).2.2.1 :=
        congrArg (fun m : GiantSignedGhostMemoryMoves s.2.2 =>
          (giantSignedGhostMemoryMoveTarget s.2.2 m).1) (giantSignedFixedGhostMove_of_move s.2.2 r)
      refine {
        pattern := pattern
        batch := batch
        history := {
          state := state
          deleted := deleted
          born := born
          sourceSmallPermutation := Fin.cons e.2.sourceSmallPermutation tail.history.sourceSmallPermutation
          targetSmallPermutation := Fin.cons e.2.targetSmallPermutation tail.history.targetSmallPermutation
          sourceBigPermutation := Fin.cons e.2.sourceBigPermutation tail.history.sourceBigPermutation
          targetBigPermutation := Fin.cons e.2.targetBigPermutation tail.history.targetBigPermutation
          auxiliary := Fin.cons e.2.auxiliary tail.history.auxiliary
          edge := Fin.cons ?_ tail.history.edge }
        first := rfl }
      exact hhead.symm ▸ e.2.choice

end
end ArtinMatthews
