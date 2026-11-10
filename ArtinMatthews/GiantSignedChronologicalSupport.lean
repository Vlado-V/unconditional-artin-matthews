module

public import ArtinMatthews.GiantSignedChronologicalWeight
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

/-! The literal coefficients impose the actual zero-residue deletions
and the old-index promotion hits and bans. These are support conditions
of the chronological sum. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}

structure GiantSignedChronologicalAdmissible (κ : Fin n → ℤ)
    (h : GiantSignedChronologicalChoices PS PB ell C batch) : Prop where
  compatible : GiantSignedChronologicalCompatible κ h
  boundary : GiantSignedChronologicalBoundary h
  deletedZeros : ∀ i g, h.deleted i g ⊆
    giantSignedGhostZeroIndices (giantSignedMemoryGroupEquiv PB (h.state i).2.2 g)
  promotion : ∀ i, GiantSignedEdgeHits (κ i * (giantSignedChronologicalProduct h i : ℤ))
      (giantSignedChronologicalGhostTarget h i.castSucc)
      (giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigTarget h i)) (h.edge i) ∧
    GiantSignedEdgePromotionBan (giantSignedChronologicalProduct h i) (h.edge i).2.1
      (giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigTarget h i))

theorem giantSignedChronologicalWeight_admissible (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (κ : Fin n → ℤ) (q : ℝ) (visitQ : Fin (n+1) → ℝ) (ρ θ : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (h : GiantSignedChronologicalChoices PS PB ell C batch)
    (hnz : giantSignedChronologicalWeight ν V κ q visitQ ρ θ ζ K h ≠ 0) :
    GiantSignedChronologicalAdmissible κ h := by
  classical
  have hcb : GiantSignedChronologicalCompatible κ h ∧ GiantSignedChronologicalBoundary h := by
    by_contra hc
    exact hnz (ite_eq_right hc)
  rw [giantSignedChronologicalWeight, ite_eq_left hcb] at hnz
  have hg := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hnz).1).2
  have he := (mul_ne_zero_iff.mp hnz).2
  refine ⟨hcb.1, hcb.2, ?_, ?_⟩
  · intro i g
    have hi := Finset.prod_ne_zero_iff.mp hg i (Finset.mem_univ i)
    rw [giantSignedChronologicalGhostCoefficient, giantSignedGhostMemoryMoveCoefficient,
      giantSignedGhostProductMoveCoefficient] at hi
    have hj := Finset.prod_ne_zero_iff.mp hi g (Finset.mem_univ g)
    by_contra hbad
    unfold giantSignedGhostMoveCoefficient at hj
    exact hj (ite_eq_right hbad)
  · intro i
    have hi := Finset.prod_ne_zero_iff.mp he i (Finset.mem_univ i)
    by_contra hbad
    unfold giantSignedChronologicalEdgeCoefficient giantSignedChronologicalEdgeMemoryCoefficient
      giantSignedEdgeMoveCoefficient at hi
    rw [ite_eq_right hbad, mul_zero, mul_zero] at hi
    exact hi rfl

end
end ArtinMatthews
