module

public import ArtinMatthews.GiantSignedEdgeColumnTests
public import ArtinMatthews.GiantSignedEdgePairingConvergence
public import ArtinMatthews.GiantSignedEdgePairingReal
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

/-! The weighted forward test is the original signed edge applied to a
real nonnegative test, with its input degree weight left outside. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {t : J → ℕ}

theorem giantSignedEdgeColumnTest_apply
    (ν : (j : J) → P j → ℝ) (V : J → ℝ) (ρ : ℝ) (d : ℤ) (D : ℕ) (v : ℝ)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℝ)
    (source : GiantSignedPrimeTuple P t) (m : GiantSignedMemory P) :
    giantSignedEdgeCoupledApply ν V ρ d (giantSignedEdgeColumnTest D v f) source m =
      v ^ (∑ j, m.1 j) *
        (giantSignedEdgeApply (fun j p => (ν j p : ℂ)) V ρ d D source
          (fun target out => (f target out : ℂ)) m).re := by
  have he : giantSignedEdgeColumnTest (P := P) D v f =
      (fun S T source target old out => v ^ (∑ j, old.1 j) *
        (if GiantSignedEdgePromotionBan D T target then f target out else 0)) := by
    funext S T source target old out
    unfold giantSignedEdgeColumnTest
    split_ifs <;> ring
  rw [he, giantSignedEdgeCoupledApply_input_mul, giantSignedEdgeApply_eq_coe_coupled]
  rfl

theorem giantSignedEdgeApply_ofReal_norm (ν : (j : J) → P j → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (V : J → ℝ) (hV : ∀ j, 0 ≤ V j)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (d : ℤ) (D : ℕ)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℝ)
    (hf : ∀ target out, 0 ≤ f target out)
    (source : GiantSignedPrimeTuple P t) (m : GiantSignedMemory P) :
    ‖giantSignedEdgeApply (fun j p => (ν j p : ℂ)) V ρ d D source
        (fun target out => (f target out : ℂ)) m‖ =
      (giantSignedEdgeApply (fun j p => (ν j p : ℂ)) V ρ d D source
        (fun target out => (f target out : ℂ)) m).re := by
  rw [giantSignedEdgeApply_eq_coe_coupled]
  have hp := giantSignedEdgeCoupledApply_nonneg ν hν V hV hρ d
    (fun _ T _ target _ out => if GiantSignedEdgePromotionBan D T target then f target out else 0)
    (fun _ _ _ target _ out => by
      split_ifs
      · exact hf target out
      · exact le_rfl) source m
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]
  rfl

end
end ArtinMatthews
