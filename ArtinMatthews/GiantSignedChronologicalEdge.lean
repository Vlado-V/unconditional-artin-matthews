module

public import ArtinMatthews.GiantSignedChronologicalWeight
public import ArtinMatthews.GiantSignedRawEdgeData
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

/-! Every supported chronological edge is an actual move of the full
raw row, with identical target and coefficient. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {S B : Type*} [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}

def giantSignedChronologicalRawMove
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (i : Fin n) :
    GiantSignedRawEdgeMove PS PB ell (C i)
      (giantSignedChronologicalAfterVisitState h i.castSucc).2.2 where
  sourceSmallPermutation := h.sourceSmallPermutation i
  sourceBigPermutation := h.sourceBigPermutation i
  targetSmallPermutation := h.targetSmallPermutation i
  targetBigPermutation := h.targetBigPermutation i
  auxiliary := h.auxiliary i
  choice := h.edge i
  smallTarget := giantSignedChronologicalSmallTarget h i
  bigTarget := giantSignedChronologicalBigTarget h i

omit [DecidableEq S] [DecidableEq B] in
theorem giantSignedChronologicalRawMove_product
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (i : Fin n) :
    giantSignedRawEdgeProduct (giantSignedChronologicalAfterVisitState h i.castSucc)
      (giantSignedChronologicalRawMove h i) = giantSignedChronologicalProduct h i := rfl

omit [DecidableEq S] [DecidableEq B] in
theorem giantSignedChronologicalRawMove_condition (κ : Fin n → ℤ)
    (h : GiantSignedChronologicalChoices PS PB ell C batch)
    (hc : GiantSignedChronologicalCompatible κ h) (i : Fin n) :
    GiantSignedRawEdgeCondition (κ i) (giantSignedChronologicalAfterVisitState h i.castSucc)
      (giantSignedChronologicalRawMove h i) := by
  exact ⟨(hc i).1, (hc i).2.1, (hc i).2.2.1,
    (hc i).2.2.2.2.1, (hc i).2.2.2.2.2⟩

omit [DecidableEq S] [DecidableEq B] in
theorem giantSignedChronologicalRawMove_target (κ : Fin n → ℤ)
    (h : GiantSignedChronologicalChoices PS PB ell C batch)
    (hc : GiantSignedChronologicalCompatible κ h) (i : Fin n) :
    giantSignedRawEdgeTarget (κ i) (giantSignedChronologicalAfterVisitState h i.castSucc)
      (giantSignedChronologicalRawMove h i) = h.state i.succ := by
  apply Prod.ext
  · exact (giantTwoSidedResiduePermute (h.targetSmallPermutation i)).symm_apply_apply _
  · apply Prod.ext
    · exact (giantSignedGroupedTuplePermutation (h.targetBigPermutation i)).symm_apply_apply _
    · exact (hc i).2.2.2.1.symm

theorem giantSignedChronologicalRawMove_coefficient (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (κ : Fin n → ℤ) (q ρ θ : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (h : GiantSignedChronologicalChoices PS PB ell C batch)
    (hc : GiantSignedChronologicalCompatible κ h) (i : Fin n) :
    giantSignedRawEdgeCoefficient ν V (κ i) q ρ θ (ζ i) (K i)
      (giantSignedChronologicalAfterVisitState h i.castSucc)
      (giantSignedChronologicalRawMove h i) =
        giantSignedChronologicalEdgeCoefficient ν V κ q ρ θ ζ K h i := by
  rw [giantSignedRawEdgeCoefficient, ite_eq_left (giantSignedChronologicalRawMove_condition κ h hc i)]
  rfl

theorem giantSignedChronologicalWeight_eq_raw (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (κ : Fin n → ℤ) (q : ℝ) (visitQ : Fin (n+1) → ℝ) (ρ θ : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (h : GiantSignedChronologicalChoices PS PB ell C batch)
    (hc : GiantSignedChronologicalCompatible κ h) (hb : GiantSignedChronologicalBoundary h) :
    giantSignedChronologicalWeight ν V κ q visitQ ρ θ ζ K h =
      (giantSignedStateMass PS ν (h.state 0) : ℂ) *
        (∏ i, giantSignedChronologicalGhostCoefficient ν V visitQ ρ h i) *
        ∏ i, giantSignedRawEdgeCoefficient ν V (κ i) q ρ θ (ζ i) (K i)
          (giantSignedChronologicalAfterVisitState h i.castSucc)
          (giantSignedChronologicalRawMove h i) := by
  rw [giantSignedChronologicalWeight, ite_eq_left ⟨hc, hb⟩]
  simp_rw [giantSignedChronologicalRawMove_coefficient ν V κ q ρ θ ζ K h hc]

end
end ArtinMatthews
