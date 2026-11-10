module

public import OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.Henselian
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
public import OAI.RepresentationTheory.Weil.Local.Analytic
public import OAI.RepresentationTheory.Weil.Local.Gaussian
public import OAI.RepresentationTheory.Weil.Local.GaussianSquareClasses


set_option backward.privateInPublic true
@[expose] public section

/-! Square-class invariance of the genuine analytic index at every local
field, including dyadic and archimedean places.  The limit is supplied by
the proved analytic local-field normalization, not a Weil-product premise. -/

namespace ArtinMatthews.QuadraticWeil

open MeasureTheory Filter
open OAI.RepresentationTheory.Weil.Local
open scoped Classical Topology

noncomputable section

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
  [MeasurableSpace k] [BorelSpace k]
  (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ)
  (hc : Continuous (fun x => ψ x)) (hu : ∀ x : k, ‖ψ x‖ = 1) (hn : ∃ x : k, ψ x ≠ 1)

include hnd hc hu hn in
theorem localGaussianIntegral_square_mul (a : k) (ha : a ≠ 0) (b : kˣ) :
    FunctionsMetaplectic.Construction.gaussianIntegral k ψ (a * (b : k) ^ 2) =
      ((FunctionsMetaplectic.Construction.localModulus k b)⁻¹ : ℝ) •
        FunctionsMetaplectic.Construction.gaussianIntegral k ψ a := by
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hnd
  have hlim := ((Analytic.Construction.localField_analytic_normalization hnd ψ hc hu hn 1).2.2.1 a ha).1.comp
    (GaussianSquareClasses.Construction.positive_division_tendsto_zero_right
      (‖(b : k)‖ ^ 2) (sq_pos_of_pos (norm_pos_iff.mpr b.ne_zero)))
  have hscaled := hlim.const_smul ((FunctionsMetaplectic.Construction.localModulus k b)⁻¹ : ℝ)
  have hresult : Tendsto (FunctionsMetaplectic.Construction.regularizedGaussian k ψ (a * (b : k) ^ 2))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((FunctionsMetaplectic.Construction.localModulus k b)⁻¹ : ℝ) •
        FunctionsMetaplectic.Construction.gaussianIntegral k ψ a)) := by
    simpa only [Function.comp_def,
      ← GaussianSquareClasses.Construction.regularizedGaussian_square_mul ψ a b] using hscaled
  exact hresult.limUnder_eq

include hnd hc hu hn in
theorem localGaussianIndex_square_mul (a : k) (ha : a ≠ 0) (b : kˣ) :
    FunctionsMetaplectic.Construction.gaussianIndex k ψ (a * (b : k) ^ 2) =
      FunctionsMetaplectic.Construction.gaussianIndex k ψ a := by
  rw [FunctionsMetaplectic.Construction.gaussianIndex,
    localGaussianIntegral_square_mul hnd ψ hc hu hn a ha b, Complex.real_smul,
    Gaussian.Construction.phase_positive_mul
      ((FunctionsMetaplectic.Construction.localModulus k b)⁻¹)
      (inv_pos.mpr (FunctionsMetaplectic.Construction.localModulus_pos k b))]
  rfl

def analyticNormalizedWeil (x : kˣ) : ℂ :=
  FunctionsMetaplectic.Construction.gaussianIndex k ψ (2 * (x : k)) /
    FunctionsMetaplectic.Construction.gaussianIndex k ψ 2

include hnd hc hu hn in
theorem analyticNormalizedWeil_square_mul (x y : kˣ) :
    analyticNormalizedWeil ψ (x * y ^ 2) = analyticNormalizedWeil ψ x := by
  have hcoeff : (2 : k) * ((x * y ^ 2 : kˣ) : k) =
      (2 * (x : k)) * (y : k) ^ 2 := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  unfold analyticNormalizedWeil
  rw [hcoeff, localGaussianIndex_square_mul hnd ψ hc hu hn _
    (mul_ne_zero (by norm_num) x.ne_zero) y]

include hnd hc hu hn in
theorem analyticNormalizedWeil_eighth (x : kˣ) : analyticNormalizedWeil ψ x ^ 8 = 1 := by
  have h := (Analytic.Construction.localField_analytic_normalization hnd ψ hc hu hn 1).2.2.1
  have hnum := (h (2 * (x : k)) (mul_ne_zero (by norm_num) x.ne_zero)).2.2
  have hden := (h 2 (by norm_num)).2.2
  rw [analyticNormalizedWeil, div_pow, hnum, hden, div_one]

end

end ArtinMatthews.QuadraticWeil
