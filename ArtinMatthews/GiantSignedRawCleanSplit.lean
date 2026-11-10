module

public import ArtinMatthews.GiantSignedRawCleanChoice
public import ArtinMatthews.GiantSignedRawEdgeSplit
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

/-! The selected clean row is the clean part of the original raw row's
proved partition, with the same coefficient and target map. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [Fintype (GiantTwoSidedResidueState PS (k+ell))]
    {C : B → Finset (Fin k)}

omit [Fintype B] [DecidableEq B] [DecidableEq S]
  [Fintype (GiantTwoSidedResidueState PS (k+ell))] in
theorem giantSignedRawEdgeClean_iff_choiceClean {m : GiantSignedMemory PB}
    (r : GiantSignedRawEdgeMove PS PB ell C m) :
    GiantSignedRawEdgeClean r ↔ GiantSignedEdgeChoiceClean r.choice := Iff.rfl

theorem giantSignedRawCleanApply_eq_split
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell)
    (f : GiantSignedState PS PB (k+ell) → ℂ) (s : GiantSignedState PS PB (k+ell)) :
    giantSignedRawCleanApply ν V κ q ρ θ ζ K f s =
      giantSignedRawEdgeApply ν V κ q ρ θ ζ K giantSignedRawEdgeCleanMultiplier f s := rfl

theorem giantSignedRawEdgeApply_one_eq_clean_add_dirty
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell)
    (f : GiantSignedState PS PB (k+ell) → ℂ) (s : GiantSignedState PS PB (k+ell)) :
    giantSignedRawEdgeApply ν V κ q ρ θ ζ K (fun _ _ => 1) f s =
      giantSignedRawCleanApply ν V κ q ρ θ ζ K f s +
        giantSignedRawEdgeApply ν V κ q ρ θ ζ K giantSignedRawEdgeDirtyMultiplier f s := by
  simpa only [one_mul, giantSignedRawCleanApply_eq_split] using
    giantSignedRawEdgeApply_clean_add_dirty ν V κ q ρ θ ζ K (fun _ _ => 1) f s

end
end ArtinMatthews
