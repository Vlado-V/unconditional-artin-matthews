module

public import OAI.NumberTheory.EgyptianFractions.RealPhaseEnvelope
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import ArtinMatthews.SourceMellinSchwartzEnergy
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Dualization of the literal local additive energy. The frequency
cutoff is an actual smooth bump, so its inverse Fourier test is Schwartz. -/

namespace ArtinMatthews
open MeasureTheory Filter Set
open scoped FourierTransform SchwartzMap ContDiff BigOperators
noncomputable section

local notation "e" => OAI.Problem337.RealPhase.phase

/-- The source additive phase uses `exp(2πi β x)`. -/
def sourceLocalAdditivePolynomial {ι : Type*} (S : Finset ι) (x : ι → ℝ) (a : ι → ℂ)
    (β : ℝ) : ℂ := ∑ i ∈ S, a i * e (β * x i)

private theorem sourceMellin_phase_contDiff : ContDiff ℝ ∞ (e : ℝ → ℂ) := by
  unfold OAI.Problem337.RealPhase.phase
  have hl : ContDiff ℝ ∞ (fun t : ℝ => 2 * Real.pi * t) := contDiff_const.mul contDiff_id
  exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hl)).cexp

theorem sourceLocalAdditivePolynomial_contDiff {ι : Type*} (S : Finset ι)
    (x : ι → ℝ) (a : ι → ℂ) : ContDiff ℝ ∞ (sourceLocalAdditivePolynomial S x a) := by
  unfold sourceLocalAdditivePolynomial
  exact ContDiff.sum fun _ _ => contDiff_const.mul
    (sourceMellin_phase_contDiff.comp (contDiff_id.mul contDiff_const))

theorem sourceLocalAdditivePolynomial_norm_le {ι : Type*} (S : Finset ι)
    (x : ι → ℝ) (a : ι → ℂ) (β : ℝ) :
    ‖sourceLocalAdditivePolynomial S x a β‖ ≤ ∑ i ∈ S, ‖a i‖ := by
  unfold sourceLocalAdditivePolynomial
  simpa only [norm_mul, OAI.Problem337.RealPhase.norm_phase, mul_one] using
    norm_sum_le S (fun i => a i * e (β * x i))

theorem sourceMellin_inverse_fourier_phase (q : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (𝓕⁻ q) x = ∫ t : ℝ, e (t * x) * q t := by
  rw [congrFun (SchwartzMap.fourierInv_coe q) x, Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [smul_eq_mul]
  congr 1
  unfold OAI.Problem337.RealPhase.phase
  congr 1
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

theorem sourceMellin_inverse_fourier_sum {ι : Type*} (S : Finset ι)
    (x : ι → ℝ) (a : ι → ℂ) (q : 𝓢(ℝ, ℂ)) :
    (∑ i ∈ S, a i * (𝓕⁻ q) (x i)) =
      ∫ t : ℝ, sourceLocalAdditivePolynomial S x a t * q t := by
  have hi (i : ι) : Integrable (fun t : ℝ => e (t * x i) * q t) := by
    apply q.integrable.norm.mono'
    · exact ((sourceMellin_phase_contDiff.continuous.comp
        (continuous_id.mul continuous_const)).mul q.continuous).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun t => by
        rw [norm_mul, OAI.Problem337.RealPhase.norm_phase, one_mul]
  simp_rw [sourceMellin_inverse_fourier_phase, ← integral_const_mul]
  rw [← integral_finsetSum S (fun i _ => (hi i).const_mul (a i))]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [sourceLocalAdditivePolynomial, Finset.sum_mul, mul_assoc]

theorem sourceAdditiveMellin_dual_test {ι : Type*} (S : Finset ι)
    (x : ι → ℝ) (a : ι → ℂ) {T : ℝ} (hT : 0 < T) :
    ∃ (q : 𝓢(ℝ, ℂ)) (E : ℝ), 0 ≤ E ∧
      (∫ t in Icc (-T) T, ‖sourceLocalAdditivePolynomial S x a t‖ ^ 2) ≤ E ∧
      (∀ t : ℝ, 2 * T < |t| → q t = 0) ∧
      (∫ t : ℝ, ‖q t‖ ^ 2) ≤ E ∧
      (∑ i ∈ S, a i * (𝓕⁻ q) (x i)) = (E : ℂ) := by
  let F := sourceLocalAdditivePolynomial S x a
  have hF := sourceLocalAdditivePolynomial_contDiff S x a
  let b : ContDiffBump (0 : ℝ) := ⟨T, 2*T, hT, by linarith⟩
  let q₀ (t : ℝ) := (b t : ℂ) * star (F t)
  have hbC : HasCompactSupport (fun t : ℝ => (b t : ℂ)) :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hqC : HasCompactSupport q₀ := hbC.mul_right
  have hqS : ContDiff ℝ ∞ q₀ :=
    (Complex.ofRealCLM.contDiff.comp b.contDiff).mul
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp hF)
  let q := hqC.toSchwartzMap hqS
  have hq (t : ℝ) : q t = (b t : ℂ) * star (F t) := rfl
  let d (t : ℝ) := b t * ‖F t‖ ^ 2
  let E := ∫ t : ℝ, d t
  have hd : Integrable d :=
    (b.continuous.mul (hF.continuous.norm.pow 2)).integrable_of_hasCompactSupport
      b.hasCompactSupport.mul_right
  have hd₀ (t : ℝ) : 0 ≤ d t := mul_nonneg b.nonneg (sq_nonneg _)
  have hE : 0 ≤ E := integral_nonneg hd₀
  refine ⟨q, E, hE, ?_, ?_, ?_, ?_⟩
  · calc
      _ = ∫ t in Icc (-T) T, d t := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro t ht
        have hb : b t = 1 := b.one_of_mem_closedBall (by
          change t ∈ Metric.closedBall 0 T
          simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using abs_le.mpr ht)
        simp only [d, hb, one_mul, F]
      _ ≤ E := setIntegral_le_integral hd (Eventually.of_forall hd₀)
  · intro t ht
    have hb : b t = 0 := Function.notMem_support.mp (by
      rw [b.support_eq]
      change t ∉ Metric.ball 0 (2*T)
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using not_lt_of_ge ht.le)
    rw [hq, hb, Complex.ofReal_zero, zero_mul]
  · apply integral_mono (sourceMellinSchwartz_norm_sq_integrable q) hd
    intro t
    have hb₀ : 0 ≤ b t := b.nonneg
    have hb₁ : b t ≤ 1 := b.le_one
    change ‖q t‖ ^ 2 ≤ b t * ‖F t‖ ^ 2
    rw [hq, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb₀, norm_star, mul_pow]
    exact mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hb₀ (sub_nonneg.mpr hb₁)]) (sq_nonneg _)
  · rw [sourceMellin_inverse_fourier_sum]
    calc
      _ = ∫ t : ℝ, (d t : ℂ) := by
        apply integral_congr_ae
        filter_upwards [] with t
        change F t * q t = _
        rw [hq, ← mul_left_comm]
        change (b t : ℂ) * (F t * (starRingEnd ℂ) (F t)) =
          ((b t * ‖F t‖ ^ 2 : ℝ) : ℂ)
        rw [Complex.mul_conj', Complex.ofReal_mul, Complex.ofReal_pow]
      _ = (E : ℂ) := Complex.ofRealCLM.integral_comp_comm hd

end
end ArtinMatthews
