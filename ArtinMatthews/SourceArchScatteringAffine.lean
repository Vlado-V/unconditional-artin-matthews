module

public import ArtinMatthews.SourceComplexTraceFourier
public import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Translation and real dilation for the actual complex trace measure. -/
namespace ArtinMatthews.SourceArchJacquet

open MeasureTheory
open ArtinMatthews.VaryingKummerAnalytic
noncomputable section

theorem sourceArchTraceIntegral_affine (f : ℂ → ℂ) (u : ℂ) {H : ℝ} (hH : 0 < H) :
    (∫ x : ℂ, f ((x + u) / (H : ℂ)) ∂sourceComplexTraceMeasure) =
      (H ^ 2 : ℝ) * ∫ x : ℂ, f x ∂sourceComplexTraceMeasure := by
  have : sourceComplexTraceMeasure.IsAddHaarMeasure := by
    exact Measure.IsAddHaarMeasure.smul volume (by norm_num : (2 : ENNReal) ≠ 0)
      (by norm_num : (2 : ENNReal) ≠ ⊤)
  have he : (fun x : ℂ => f ((x + u) / (H : ℂ))) =
      (fun x : ℂ => f ((H⁻¹ : ℝ) • (x + u))) := by
    funext x
    congr 1
    rw [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
    ring
  rw [he, integral_add_right_eq_self (fun x : ℂ => f ((H⁻¹ : ℝ) • x)) u,
    Measure.integral_comp_smul sourceComplexTraceMeasure f H⁻¹]
  simp [Complex.finrank_real_complex, inv_pow, abs_of_nonneg (sq_pos_of_pos hH).le]

theorem sourceArchTraceIntegrable_affine (f : ℂ → ℂ) (u : ℂ) {H : ℝ} (hH : 0 < H)
    (hf : Integrable f sourceComplexTraceMeasure) :
    Integrable (fun x : ℂ => f ((x + u) / (H : ℂ))) sourceComplexTraceMeasure := by
  have : sourceComplexTraceMeasure.IsAddHaarMeasure := by
    exact Measure.IsAddHaarMeasure.smul volume (by norm_num : (2 : ENNReal) ≠ 0)
      (by norm_num : (2 : ENNReal) ≠ ⊤)
  have h := (hf.comp_smul (inv_ne_zero hH.ne')).comp_add_right u
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  congr 1
  rw [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
  ring

end
end ArtinMatthews.SourceArchJacquet
