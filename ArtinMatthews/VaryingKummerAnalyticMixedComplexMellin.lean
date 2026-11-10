module

public import ArtinMatthews.VaryingKummerAnalyticMixedPartialDedekind
public import ArtinMatthews.VaryingKummerAnalyticMixedThetaPositive
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual complex Mellin kernel of the mixed ideal theta, including the exact
positive majorant supplied by the already proved real Mellin identity. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField MeasureTheory Set Filter
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open ArtinMatthews.ReusedTheta
open scoped NumberField nonZeroDivisors Classical BigOperators ENNReal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

theorem mixedIdealFlowTheta_sub_one_real (u : logSpace K) {t : ℝ} (ht : 0 < t) :
    mixedIdealFlowTheta K I u t - 1 =
      (((mixedIdealFlowTheta K I u t - 1).re : ℝ) : ℂ) := by
  rw [mixedIdealFlowTheta_eq_normalizedTheta]
  let B := logScaledLattice (mixedIdealMatrix K I) (mixedIdealLogScale K I u)
  change normalizedTheta B t - 1 = (((normalizedTheta B t - 1).re : ℝ) : ℂ)
  rw [normalizedTheta, ← thetaRemainder_eq B (mul_pos Real.pi_pos ht),
    thetaRemainder_eq_real_sum B ht, Complex.ofReal_re]

theorem mixedIdealFlowTheta_sub_one_norm (u : logSpace K) {t : ℝ} (ht : 0 < t) :
    ‖mixedIdealFlowTheta K I u t - 1‖ = (mixedIdealFlowTheta K I u t - 1).re := by
  rw [mixedIdealFlowTheta_eq_normalizedTheta]
  let B := logScaledLattice (mixedIdealMatrix K I) (mixedIdealLogScale K I u)
  change ‖normalizedTheta B t - 1‖ = (normalizedTheta B t - 1).re
  rw [normalizedTheta, ← thetaRemainder_eq B (mul_pos Real.pi_pos ht),
    thetaRemainder_eq_real_sum B ht, Complex.ofReal_re, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg (fun _ => (Real.exp_pos _).le))]

theorem mixedIdealFlowTheta_joint_measurable :
    Measurable (fun p : ℝ × logSpace K => mixedIdealFlowTheta K I p.2 p.1) := by
  let : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let : Countable I.1 := Subtype.val_injective.countable
  unfold mixedIdealFlowTheta
  apply Measurable.tsum
  intro a
  simp_rw [← Complex.ofReal_pow, mixedIdealFlow_norm_sq]
  change Measurable (fun p : ℝ × logSpace K =>
    Complex.exp (-((Real.pi*p.1 : ℝ) : ℂ) * (mixedArchEnergy K (a : K) p.2 : ℂ)))
  have he := mixedArchEnergy_continuous K (a : K)
  fun_prop

def mixedThetaMellinKernel (s : ℂ) (p : ℝ × logSpace K) : ℂ :=
  (p.1 : ℂ)^((Module.finrank ℚ K : ℂ)*s/2-1) *
    (mixedIdealFlowTheta K I p.2 p.1 - 1)

theorem mixedThetaMellinKernel_measurable (s : ℂ) :
    Measurable (mixedThetaMellinKernel K I s) := by
  unfold mixedThetaMellinKernel
  exact (by fun_prop : Measurable (fun p : ℝ × logSpace K =>
    (p.1 : ℂ)^((Module.finrank ℚ K : ℂ)*s/2-1))).mul
      ((mixedIdealFlowTheta_joint_measurable K I).sub measurable_const)

theorem mixedThetaMellinKernel_norm (s : ℂ) {t : ℝ} (ht : 0 < t) (u : logSpace K) :
    ‖mixedThetaMellinKernel K I s (t,u)‖ =
      t^((Module.finrank ℚ K : ℝ)*s.re/2-1) * (mixedIdealFlowTheta K I u t - 1).re := by
  rw [mixedThetaMellinKernel, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
    mixedIdealFlowTheta_sub_one_norm K I u ht]
  simp only [Complex.sub_re, Complex.mul_re, Complex.div_ofNat_re,
    Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero, Complex.one_re]

theorem mixedThetaMellinKernel_enorm_integral (s : ℂ) (hs : 0 < s.re) :
    (∫⁻ p, ‖mixedThetaMellinKernel K I s p‖ₑ
      ∂(volume.restrict (Ioi 0)).prod (volume.restrict (mixedUnitLogDomain K))) =
      (torsionOrder K : ℝ≥0∞) *
        ENNReal.ofReal (mixedRealHeckeFactor K s.re * (FractionalIdeal.absNorm I.1 : ℝ)^(-s.re)) *
        mixedPartialDedekindPositive K I s.re := by
  rw [lintegral_prod _ (mixedThetaMellinKernel_measurable K I s).enorm.aemeasurable]
  rw [← mixedIdealFlowTheta_mellin_positive K I hs]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro u
  rw [← ofReal_norm, mixedThetaMellinKernel_norm K I s ht u,
    ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]

end
end ArtinMatthews.VaryingKummerAnalytic
