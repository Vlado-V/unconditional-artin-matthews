module

public import ArtinMatthews.GiantFixedResiduePolynomial
public import ArtinMatthews.MarkedProgressionWeightedModel
public import ArtinMatthews.GiantFixedResidueResidual
public import ArtinMatthews.MarkedProgressionCoprime
public import ArtinMatthews.MarkedProgressionResidualBounds
public import ArtinMatthews.MarkedProgressionScaling
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! The fixed unit progression retains the same explicit marking-layer
mass estimates, with the exact fixed-modulus main term. -/
namespace ArtinMatthews
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem giantFixedResidue_weighted_residual_quantitative (M a : ℕ)
    (hM : 0<M) (ha : a.Coprime M) (P S : Finset ℕ) (hcop : ∀p∈P,p.Coprime M)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) (θ : ℕ → ℝ)
    (hθ : ∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) (m R : ℕ)
    {y V : ℝ} (hy : 0 < y) (hmin : ∀ p ∈ P, y ≤ (p : ℝ)) (hV : 0 ≤ V)
    (hmass : ∑ p ∈ P \ S, θ p / (p : ℝ) ≤ V)
    (f : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (hf : Differentiable ℝ f)
    (hderiv : Continuous (deriv f)) (hfT : f T = 0) (hf0 : ∀ t, 0 ≤ f t) :
    (∑ r ∈ Finset.Icc 1 R,
      |(∑ u ∈ giantFixedResidueSet M a r T,
          f u * markedWeightedResidual P S θ u) -
        giantFixedResidueScale M r (∫ t in Set.Ioc 0 T, f t) * markedWeightedModel P S θ|) ≤
      (R : ℝ) * (3 * ∫ t in Set.Ioc 0 T, |deriv f t|) *
        (((2 * m + 1 : ℕ) : ℝ) * (max 1 ((P \ S).card : ℝ)) ^ (2 * m) +
          (max 1 ((P \ S).card : ℝ)) ^ (2 * m + 1)) +
      ((∫ t in Set.Ioc 0 T, f t) * (harmonic R : ℝ)) *
        (1 / (∏ p ∈ S, p : ℕ)) *
        ((((S.card + 2 * m : ℕ) : ℝ) / y) * Real.exp V +
          2 * (V ^ (2 * m + 1) / (2 * m + 1).factorial)) := by
  have h0 := giantFixedResidue_weighted_residual_summed_error M a hM ha P S hcop hP hS θ hθ m R f hT hf hderiv hfT hf0
  have hC := markedWeightedCoefficient_mass_le P S θ hθ (2 * m)
  have hD := markedWeightedTailCoefficientMass_le P S θ hθ (2 * m + 1)
  have hL := markedWeightedLocalMass_le P S hP hS θ (fun p hp => (hθ p hp).1) (2 * m)
    hy hmin hmass
  have hM := markedWeightedTailModel_le P S θ (fun p hp => (hθ p hp).1)
    (2 * m + 1) hV hmass
  have hI : 0 ≤ ∫ t in Set.Ioc 0 T, f t := MeasureTheory.integral_nonneg hf0
  have hVar : 0 ≤ ∫ t in Set.Ioc 0 T, |deriv f t| :=
    MeasureTheory.integral_nonneg (fun _ => abs_nonneg _)
  have hH : 0 ≤ (harmonic R : ℝ) := by
    rw [← reciprocal_Icc_eq_harmonic]
    exact Finset.sum_nonneg (fun r _ => by positivity)
  apply h0.trans
  calc
    _ ≤ (R : ℝ) * (3 * ∫ t in Set.Ioc 0 T, |deriv f t|) *
        (((2 * m + 1 : ℕ) : ℝ) * (max 1 ((P \ S).card : ℝ)) ^ (2 * m) +
          (max 1 ((P \ S).card : ℝ)) ^ (2 * m + 1)) +
      ((∫ t in Set.Ioc 0 T, f t) * (harmonic R : ℝ)) *
        ((((S.card + 2 * m : ℕ) : ℝ) / y) * (1 / (∏ p ∈ S, p : ℕ)) * Real.exp V +
          2 * ((1 / (∏ p ∈ S, p : ℕ)) * (V ^ (2 * m + 1) / (2 * m + 1).factorial))) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (add_le_add hC hD) (by positivity)
      · exact mul_le_mul_of_nonneg_left
          (add_le_add hL (mul_le_mul_of_nonneg_left hM (by norm_num))) (mul_nonneg hI hH)
    _ = _ := by ring

/-- Exact scale-`x` version used by the marked predecessor progression
estimate. Only the main integral acquires a factor of `x`. -/
theorem giantFixedResidue_weighted_residual_rescaled_quantitative (M a : ℕ)
    (hM : 0<M) (ha : a.Coprime M) (P S : Finset ℕ) (hcop : ∀p∈P,p.Coprime M)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) (θ : ℕ → ℝ)
    (hθ : ∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) (m R : ℕ)
    {y V : ℝ} (hy : 0 < y) (hmin : ∀ p ∈ P, y ≤ (p : ℝ)) (hV : 0 ≤ V)
    (hmass : ∑ p ∈ P \ S, θ p / (p : ℝ) ≤ V)
    (Φ : ℝ → ℝ) {x T : ℝ} (hx : 0 < x) (hT : 0 ≤ T) (hΦ : Differentiable ℝ Φ)
    (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0) (hΦ0 : ∀ t, 0 ≤ Φ t) :
    (∑ r ∈ Finset.Icc 1 R,
      |(∑ u ∈ giantFixedResidueSet M a r (T*x),
          Φ ((u : ℝ) / x) * markedWeightedResidual P S θ u) -
        giantFixedResidueScale M r (x * ∫ t in Set.Ioc 0 T, Φ t) * markedWeightedModel P S θ|) ≤
      (R : ℝ) * (3 * ∫ t in Set.Ioc 0 T, |deriv Φ t|) *
        (((2 * m + 1 : ℕ) : ℝ) * (max 1 ((P \ S).card : ℝ)) ^ (2 * m) +
          (max 1 ((P \ S).card : ℝ)) ^ (2 * m + 1)) +
      ((x * ∫ t in Set.Ioc 0 T, Φ t) * (harmonic R : ℝ)) *
        (1 / (∏ p ∈ S, p : ℕ)) *
        ((((S.card + 2 * m : ℕ) : ℝ) / y) * Real.exp V +
          2 * (V ^ (2 * m + 1) / (2 * m + 1).factorial)) := by
  have h := giantFixedResidue_weighted_residual_quantitative M a hM ha P S hcop hP hS θ hθ m R hy hmin hV hmass
    (fun u => Φ (u / x)) (mul_nonneg hT hx.le) (marked_rescale_differentiable Φ x hΦ)
    (marked_rescale_deriv_continuous Φ x hΦ hderiv)
    (by rw [marked_rescale_endpoint Φ hx T, hΦT]) (fun u => hΦ0 (u / x))
  rw [marked_rescale_integral Φ hx hT, marked_rescale_variation Φ hx hT hΦ] at h
  exact h

end
end ArtinMatthews
