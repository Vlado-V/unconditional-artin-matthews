module

public import ArtinMatthews.SpectralKLWeightedMeasures
public import ArtinMatthews.EllipticFiveEighthsMoment
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Weighted physical moments replace a positive lower support bound
in the actual folded orbital kernel. -/

noncomputable section
open Set MeasureTheory Filter
namespace ArtinMatthews

def spectralWeylPhysicalMoment (B : ℝ) (g : ℝ → ℂ) : ℝ :=
  ∫ x : ℝ, x^(-B)*‖g x‖ ∂spectralKLPhysicalMeasure

theorem spectralWeylPhysicalMoment_integrable_iff (B : ℝ) (g : ℝ → ℂ) :
    Integrable (fun x : ℝ => x^(-B)*‖g x‖) spectralKLPhysicalMeasure ↔
      IntegrableOn (fun x : ℝ => x^(-B)*‖g x‖/x) (Ioi (0 : ℝ)) := by
  have he : (fun x : ℝ => x⁻¹*(x^(-B)*‖g x‖)) =
      (fun x : ℝ => x^(-B)*‖g x‖/x) := by
    funext x
    ring
  change Integrable _ (spectralKLPositiveWeightMeasure (fun x => x⁻¹)) ↔ _
  rw [spectralKLPositiveWeightMeasure_integrable_iff _ _ (by fun_prop)
    (fun x hx => inv_nonneg.mpr hx.le),he]

theorem spectralWeylPhysicalMoment_eq (B : ℝ) (g : ℝ → ℂ) :
    spectralWeylPhysicalMoment B g =
      ∫ x : ℝ in Ioi (0 : ℝ), x^(-B)*‖g x‖/x := by
  unfold spectralWeylPhysicalMoment spectralKLPhysicalMeasure
  rw [spectralKLPositiveWeightMeasure_integral _ _ (by fun_prop)
    (fun x hx => inv_nonneg.mpr hx.le)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  ring

theorem spectralWeylPhysicalMoment_nonneg (B : ℝ) (g : ℝ → ℂ) :
    0 ≤ spectralWeylPhysicalMoment B g := by
  apply integral_nonneg_of_ae
  filter_upwards [spectralKLPositiveWeightMeasure_ae_pos (fun x => x⁻¹)] with x hx
  exact mul_nonneg (Real.rpow_nonneg hx.le _) (norm_nonneg _)

theorem spectralWeylPhysicalMoment_five_eighths (g : ℝ → ℂ) (hg : Measurable g)
    (C : ℝ) (hC : 0 ≤ C)
    (hsmall : ∀ x : ℝ, 0 < x → x ≤ 1 → ‖g x‖ ≤ C*x^(3/4 : ℝ))
    (hlarge : ∀ x : ℝ, 1 ≤ x → ‖g x‖ ≤ C/x^2) :
    Integrable (fun x : ℝ => x^(-(5/8 : ℝ))*‖g x‖) spectralKLPhysicalMeasure ∧
      spectralWeylPhysicalMoment (5/8) g ≤ C*(8+8/21) := by
  obtain ⟨hi,hb⟩ := elliptic_five_eighths_moment g hg C hC hsmall hlarge
  exact ⟨(spectralWeylPhysicalMoment_integrable_iff _ _).mpr (by simpa only [neg_div] using hi),
    (spectralWeylPhysicalMoment_eq _ _).trans_le (by simpa only [neg_div] using hb)⟩

theorem spectralWeylFiveEighths_global_power (f : ℝ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hsmall : ∀ x : ℝ, 0 < x → x ≤ 1 → ‖f x‖ ≤ C*x^(3/4 : ℝ))
    (hlarge : ∀ x : ℝ, 1 ≤ x → ‖f x‖ ≤ C/x^2) :
    ∀ x : ℝ, 0 < x → ‖f x‖ ≤ C*x^(5/8 : ℝ) := by
  intro x hx
  by_cases hx₁ : x ≤ 1
  · exact (hsmall x hx hx₁).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hx hx₁ (by norm_num)) hC)
  · have hx₁' : 1 ≤ x := le_of_not_ge hx₁
    calc
      _ ≤ C/x^2 := hlarge x hx₁'
      _ = C*x^(-2 : ℝ) := by rw [Real.rpow_neg hx.le,Real.rpow_two]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx₁' (by norm_num)) hC

end ArtinMatthews
