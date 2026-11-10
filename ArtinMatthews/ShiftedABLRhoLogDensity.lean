module

public import ArtinMatthews.CircleNormalizerSmooth
public import OAI.NumberTheory.DirichletL.Mellin.LogProfiles
public import ArtinMatthews.ShiftedLogSeparationUniform
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
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


set_option backward.privateInPublic true
@[expose] public section

/-! The literal circle profile in log scale and its fixed Schwartz Fourier
density. Mellin heights act by a translation of the Fourier parameter. -/

noncomputable section
open Set MeasureTheory OAI
open scoped ContDiff FourierTransform SchwartzMap InnerProductSpace
namespace ArtinMatthews

def shiftedABLRhoLogBase (v : ℝ) : ℂ :=
  ((circleSmoothCutoff (3*Real.exp (-v))*Real.exp v : ℝ) : ℂ)

theorem shiftedABLRhoLogBase_contDiff : ContDiff ℝ ∞ shiftedABLRhoLogBase := by
  unfold shiftedABLRhoLogBase
  exact Complex.ofRealCLM.contDiff.comp
    ((circleSmoothCutoff_contDiff.comp (by fun_prop)).mul (by fun_prop))

theorem shiftedABLRhoLogBase_support :
    Function.support shiftedABLRhoLogBase ⊆ Icc (-Real.log 2) 0 := by
  intro v hv
  have hCut : 3*Real.exp (-v) ∈ Function.support circleSmoothCutoff := by
    intro h
    apply hv
    simp [shiftedABLRhoLogBase,h]
  rw [circleSmoothCutoff_support] at hCut
  have hlo : 1 < Real.exp (-v) := by linarith [hCut.1]
  have hhi : Real.exp (-v) < 2 := by linarith [hCut.2]
  have hl : -v < Real.log 2 := Real.exp_lt_exp.mp (by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using hhi)
  have hh : (0 : ℝ) < -v := Real.exp_lt_exp.mp (by simpa only [Real.exp_zero] using hlo)
  exact ⟨by linarith,by linarith⟩

def shiftedABLRhoLogBaseSchwartz : SchwartzMap ℝ ℂ :=
  (HasCompactSupport.of_support_subset_isCompact isCompact_Icc shiftedABLRhoLogBase_support).toSchwartzMap
    shiftedABLRhoLogBase_contDiff

def shiftedABLRhoFourierDensity : SchwartzMap ℝ ℂ :=
  𝓕 shiftedABLRhoLogBaseSchwartz

theorem shiftedABLRhoLogBase_inverse (v : ℝ) :
    shiftedABLRhoLogBase v =
      ∫ t : ℝ, shiftedABLRhoFourierDensity t*FourierBridge.logPhase t v := by
  calc
    _ = ∫ t : ℝ, Complex.exp (((2*Real.pi*inner ℝ t v : ℝ) : ℂ)*Complex.I)*
        shiftedABLRhoFourierDensity t :=
      FourierBridge.schwartz_log_inversion shiftedABLRhoLogBaseSchwartz v
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      rw [FourierBridge.logPhase]
      simp only [RCLike.inner_apply,conj_trivial]
      ring_nf

def shiftedABLRhoHeight (z : ℝ × ℝ) : ℝ := 2*(z.1+z.2)

def shiftedABLRhoLogProfile (z : ℝ × ℝ) (v : ℝ) : ℂ :=
  shiftedABLRhoLogBase v*FourierBridge.logPhase (shiftedABLRhoHeight z) v

theorem shiftedABLRhoLogProfile_inverse (z : ℝ × ℝ) (v : ℝ) :
    shiftedABLRhoLogProfile z v =
      ∫ t : ℝ, shiftedABLRhoFourierDensity t*FourierBridge.logPhase (t+shiftedABLRhoHeight z) v := by
  rw [shiftedABLRhoLogProfile,shiftedABLRhoLogBase_inverse,← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with t
  rw [mul_assoc]
  congr 1
  unfold FourierBridge.logPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

def shiftedABLRhoFourierMoment (J : ℕ) : ℝ :=
  ∫ t : ℝ, (1+‖t‖)^J*‖shiftedABLRhoFourierDensity t‖

theorem shiftedABLRhoFourier_shiftedMoment_le (z : ℝ × ℝ) (J : ℕ) :
    Integrable (fun t : ℝ => (1+‖t+shiftedABLRhoHeight z‖)^J*‖shiftedABLRhoFourierDensity t‖) ∧
      (∫ t : ℝ, (1+‖t+shiftedABLRhoHeight z‖)^J*‖shiftedABLRhoFourierDensity t‖) ≤
        (1+2*(‖z.1‖+‖z.2‖))^J*shiftedABLRhoFourierMoment J := by
  let B := 1+2*(‖z.1‖+‖z.2‖)
  let b := shiftedABLRhoFourierDensity
  let u := shiftedABLRhoHeight z
  let f (t : ℝ) := (1+‖t+u‖)^J*‖b t‖
  let g (t : ℝ) := B^J*((1+‖t‖)^J*‖b t‖)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hB₁ : 1 ≤ B := le_add_of_nonneg_right (by positivity : 0 ≤ 2*(‖z.1‖+‖z.2‖))
  have hu : ‖u‖ ≤ 2*(‖z.1‖+‖z.2‖) := by
    dsimp only [u,shiftedABLRhoHeight]
    rw [norm_mul,show ‖(2 : ℝ)‖ = 2 by norm_num]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
  have hLe (t : ℝ) : f t ≤ g t := by
    have h : 1+‖t+u‖ ≤ B*(1+‖t‖) := by
      calc
        _ ≤ 1+(‖t‖+‖u‖) := add_le_add le_rfl (norm_add_le _ _)
        _ ≤ B+‖t‖ := by dsimp only [B]; linarith
        _ ≤ _ := by
          rw [mul_add,mul_one]
          exact add_le_add le_rfl (le_mul_of_one_le_left (norm_nonneg t) hB₁)
    dsimp only [f,g]
    rw [← mul_assoc,← mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h J) (norm_nonneg _)
  have hG : Integrable g := (shifted_log_coefficient_moment_integrable b J).const_mul (B^J)
  have hm : AEStronglyMeasurable f := by
    unfold f
    exact ((continuous_const.add (continuous_id.add continuous_const).norm).pow J).mul b.continuous.norm
      |>.aestronglyMeasurable
  have hF : Integrable f := hG.mono' hm (ae_of_all _ (fun t => by
    rw [Real.norm_of_nonneg (show 0 ≤ f t by dsimp only [f]; positivity)]
    exact hLe t))
  refine ⟨hF,(integral_mono hF hG hLe).trans_eq ?_⟩
  exact integral_const_mul _ _

end ArtinMatthews
