module

public import ArtinMatthews.PrincipalDedekindReciprocal
public import OAI.NumberTheory.DirichletL.ContinuationContour
public import OAI.NumberTheory.DirichletL.ContinuationInversion
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The Gaussian signal of the genuine pole-removed Dedekind reciprocal.
All proved contour shifts remain in the half-plane of absolute convergence. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField MeasureTheory Set Filter Asymptotics Complex
open OAI.SevenEighths.Continuation
open scoped NumberField nonZeroDivisors Classical Topology FourierTransform
noncomputable section

def principalGaussianEndpointConstant (K : Type*) [Field K] [NumberField K] (B : ℝ) : ℝ :=
  ‖(1/(2*Real.pi) : ℂ)‖ * Real.exp ((B-5/6)^2) * principalDedekindReciprocalBound K *
    ∫ y : ℝ, Real.exp (-(y^2))

theorem principalGaussianEndpointConstant_nonneg (K : Type*) [Field K] [NumberField K]
    (B : ℝ) : 0 ≤ principalGaussianEndpointConstant K B := by
  unfold principalGaussianEndpointConstant
  have hg : 0 ≤ ∫ y : ℝ, Real.exp (-(y^2)) := integral_nonneg (fun _ => (Real.exp_pos _).le)
  have hC := (principalDedekindReciprocalBound_pos K).le
  positivity

variable (K : Type*) [Field K] [NumberField K]

def principalGaussianAmplitude (s : ℂ) : ℂ :=
  Complex.exp ((s-5/6)^2) * principalDedekindReciprocal K s

def principalGaussianSignal (c x : ℝ) : ℂ :=
  (x : ℂ)^(c : ℂ) * mellinInv (-2) (fun s => principalGaussianAmplitude K (-s)) x

theorem principalGaussianSignal_normalized (c : ℝ) {x : ℝ} (hx : 0 < x) :
    normalizedSignal (principalGaussianSignal K c) c x =
      mellinInv (-2) (fun s => principalGaussianAmplitude K (-s)) x := by
  unfold normalizedSignal principalGaussianSignal
  simp only [smul_eq_mul,←mul_assoc]
  rw [Complex.cpow_neg,inv_mul_cancel₀]
  · simp
  · exact (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [hx.ne'])

theorem principalGaussianSignal_eq_contour (c : ℝ) {x : ℝ} (hx : 0 < x) :
    principalGaussianSignal K c x = (1/(2*Real.pi) : ℂ) *
      ∫ y : ℝ, gaussianContourIntegrand (principalDedekindReciprocal K) c x ((2 : ℂ)+y*I) := by
  unfold principalGaussianSignal mellinInv
  simp only [smul_eq_mul,Complex.real_smul,Complex.ofReal_div,Complex.ofReal_mul,
    Complex.ofReal_ofNat,Complex.ofReal_one]
  rw [mul_left_comm,←integral_const_mul]
  congr 1
  rw [←integral_neg_eq_self]
  apply integral_congr_ae
  filter_upwards [] with y
  unfold gaussianContourIntegrand principalGaussianAmplitude
  have he : -(((-2 : ℝ) : ℂ)+(-y : ℝ)*I) = (2 : ℂ)+y*I := by push_cast; ring
  rw [he,←mul_assoc,←Complex.cpow_add]
  · ring_nf
  · exact Complex.ofReal_ne_zero.mpr hx.ne'


theorem principalGaussianAmplitude_differentiableAt {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (principalGaussianAmplitude K) s :=
  (((differentiable_id.sub_const (5/6 : ℂ)).pow 2).cexp.differentiableAt).mul
    (principalDedekindReciprocal_differentiableAt K hs)

theorem principalGaussianAmplitude_continuous_line (a : ℝ) (ha : 1 < a) :
    Continuous (fun y : ℝ => principalGaussianAmplitude K ((a : ℂ)+y*I)) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  have hd := principalGaussianAmplitude_differentiableAt K
    (s := (a : ℂ)+y*I) (by simpa using ha)
  exact hd.continuousAt.comp (f := fun v : ℝ => (a : ℂ)+v*I)
    (by fun_prop : ContinuousAt (fun v : ℝ => (a : ℂ)+v*I) y)

theorem principalGaussianAmplitude_norm_bound (a y : ℝ) (ha : 2 ≤ a) :
    ‖principalGaussianAmplitude K ((a : ℂ)+y*I)‖ ≤
      (Real.exp ((a-5/6)^2)*principalDedekindReciprocalBound K)*Real.exp (-(y^2)) := by
  have hn := norm_gaussianContourIntegrand (principalDedekindReciprocal K) 0 a y
    (Z := 1) zero_lt_one
  simp only [gaussianContourIntegrand,Complex.ofReal_one,Complex.ofReal_zero,
    add_zero,Complex.one_cpow,one_mul,Real.one_rpow] at hn
  change ‖principalGaussianAmplitude K ((a : ℂ)+y*I)‖ = _ at hn
  rw [hn]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_left
    (principalDedekindReciprocal_norm_le K (by simpa using (show (5/4 : ℝ) ≤ a by linarith)))
    (Real.exp_pos _).le

theorem principalGaussianAmplitude_integrable_line (a : ℝ) (ha : 2 ≤ a) :
    Integrable (fun y : ℝ => principalGaussianAmplitude K ((a : ℂ)+y*I)) :=
  integrable_of_gaussian_bound _ _
    (principalGaussianAmplitude_continuous_line K a (by linarith)).aestronglyMeasurable
    (fun y => principalGaussianAmplitude_norm_bound K a y ha)

theorem principalGaussianSignal_contour_shift (c B : ℝ) (hB : 2 ≤ B)
    {x : ℝ} (hx : 0 < x) :
    principalGaussianSignal K c x = (1/(2*Real.pi) : ℂ) *
      ∫ y : ℝ, gaussianContourIntegrand (principalDedekindReciprocal K) c x ((B : ℂ)+y*I) := by
  rw [principalGaussianSignal_eq_contour K c hx]
  congr 1
  apply vertical_integral_eq_of_gaussian_bound (C :=
    max (x^(2+c)) (x^(B+c))*Real.exp ((B-5/6)^2)*principalDedekindReciprocalBound K) _ hB
  · apply gaussianContourIntegrand_differentiableOn _ c hx
    intro z hz
    exact (principalDedekindReciprocal_differentiableAt K (by linarith [hz.1])).differentiableWithinAt
  · intro a ha y
    rw [norm_gaussianContourIntegrand _ _ _ _ hx]
    have hxpow : x^(a+c) ≤ max (x^(2+c)) (x^(B+c)) := by
      by_cases hx1 : x ≤ 1
      · exact (Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith [ha.1])).trans
          (le_max_left _ _)
      · exact (Real.rpow_le_rpow_of_exponent_le (le_of_lt (lt_of_not_ge hx1))
          (by linarith [ha.2])).trans (le_max_right _ _)
    have hexp : Real.exp ((a-5/6)^2) ≤ Real.exp ((B-5/6)^2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [ha.1,ha.2]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    have hmax : 0 ≤ max (x^(2+c)) (x^(B+c)) :=
      (Real.rpow_nonneg hx.le _).trans (le_max_left _ _)
    have hrec : ‖principalDedekindReciprocal K ((a : ℂ)+y*I)‖ ≤ principalDedekindReciprocalBound K :=
      principalDedekindReciprocal_norm_le K (by simpa using
        (show (5/4 : ℝ) ≤ a by linarith [ha.1]))
    exact mul_le_mul (mul_le_mul hxpow hexp (Real.exp_pos _).le hmax) hrec
      (norm_nonneg _) (mul_nonneg hmax (Real.exp_pos _).le)

theorem principalGaussianSignal_bound_at_zero (c B : ℝ) (hB : 2 ≤ B)
    {x : ℝ} (hx : 0 < x) :
    ‖principalGaussianSignal K c x‖ ≤ principalGaussianEndpointConstant K B*x^(B+c) := by
  rw [principalGaussianSignal_contour_shift K c B hB hx,norm_mul]
  have hg : Integrable (fun y : ℝ => Real.exp (-(y^2))) := by
    simpa using integrable_exp_neg_mul_sq (b := 1) (by norm_num)
  have hint := norm_integral_le_of_norm_le
    (hg.const_mul (x^(B+c)*Real.exp ((B-5/6)^2)*principalDedekindReciprocalBound K))
    (f := fun y : ℝ => gaussianContourIntegrand (principalDedekindReciprocal K) c x ((B : ℂ)+y*I))
    (ae_of_all _ (fun y => by
      rw [norm_gaussianContourIntegrand _ _ _ _ hx]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_left
        (principalDedekindReciprocal_norm_le K (by simpa using (show (5/4 : ℝ) ≤ B by linarith)))
        (mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_pos _).le)))
  have H := mul_le_mul_of_nonneg_left hint (norm_nonneg (1/(2*Real.pi) : ℂ))
  rw [integral_const_mul] at H
  convert H using 1
  unfold principalGaussianEndpointConstant
  ring

theorem principalGaussianSignal_rapidDecayAtZero (c : ℝ) :
    RapidDecayAtZero (principalGaussianSignal K c) := by
  intro R
  let B : ℝ := max 2 (R-c)
  apply IsBigO.of_bound (principalGaussianEndpointConstant K B)
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds
    (Iic_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with x hx hx1
  have hpow : x^(B+c) ≤ x^R := Real.rpow_le_rpow_of_exponent_ge hx hx1
    (by dsimp [B]; linarith [le_max_right (2 : ℝ) (R-c)])
  have H := (principalGaussianSignal_bound_at_zero K c B (le_max_left _ _) hx).trans
    (mul_le_mul_of_nonneg_left hpow (principalGaussianEndpointConstant_nonneg K B))
  simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hx.le R)] using H

theorem principalGaussianAmplitude_analyticAt {s : ℂ}
    (hs : principalDedekindRegularized K s ≠ 0) :
    AnalyticAt ℂ (principalGaussianAmplitude K) s := by
  exact (((analyticAt_id.sub analyticAt_const).pow 2).cexp).mul
    (principalDedekindReciprocal_analyticAt K hs)

theorem principalGaussianAmplitude_analyticAt_one :
    AnalyticAt ℂ (principalGaussianAmplitude K) 1 :=
  principalGaussianAmplitude_analyticAt K (principalDedekindRegularized_one_ne_zero K)

theorem principalGaussianAmplitude_one :
    principalGaussianAmplitude K 1 =
      Complex.exp (((1 : ℂ)-5/6)^2) * (dedekindZeta_residue K : ℂ)⁻¹ := by
  rw [principalGaussianAmplitude, principalDedekindReciprocal_one]

def principalZetaGaussianAmplitude (s : ℂ) : ℂ :=
  Complex.exp ((s-5/6)^2) * (mixedDedekindZeta K s)⁻¹

/-- The unregularized reciprocal amplitude includes this exact linear
factor. At one it vanishes while the regularized amplitude has its filled value. -/
theorem principalZetaGaussianAmplitude_eq_regularized (s : ℂ) :
    principalZetaGaussianAmplitude K s = (s-1) * principalGaussianAmplitude K s := by
  rw [principalZetaGaussianAmplitude, mixedDedekindZeta_inv_eq_regularized]
  unfold principalGaussianAmplitude
  ring

theorem principalGaussianAmplitude_eq_zeta_div {s : ℂ} (hs : s ≠ 1) :
    principalGaussianAmplitude K s = principalZetaGaussianAmplitude K s / (s-1) := by
  rw [principalZetaGaussianAmplitude_eq_regularized]
  exact (mul_div_cancel_left₀ _ (sub_ne_zero.mpr hs)).symm

theorem principalGaussianAmplitude_eq_eulerLog {s : ℂ} (hs : 1 < s.re) :
    principalGaussianAmplitude K s =
      Complex.exp ((s-5/6)^2) * Complex.exp (-dedekindEulerLog K s) / (s-1) := by
  rw [principalGaussianAmplitude, principalDedekindReciprocal_eq_exp_neg_eulerLog K hs]
  ring

end
end ArtinMatthews.VaryingKummerAnalytic
