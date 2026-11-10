module

public import ArtinMatthews.HeckeIntervalCutoff
public import OAI.NumberTheory.DirichletL.PrimeLogProfile
public import ArtinMatthews.HeckeIntervalFourier
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! Quantitative Mellin conversion for the actual moving interval cutoff
and the logarithmic division profile used by the Hecke prime theorem. -/

noncomputable section
namespace ArtinMatthews
open OAI OAI.SevenEighths MeasureTheory
open scoped ContDiff FourierTransform

def heckeIntervalLogFactor (p : ℝ×ℝ) (s : ℝ) : ℂ :=
  Real.exp (-p.2*s) • ((p.1 : ℂ)*PrimeLogProfile.safeInverse (1-p.1*s))

theorem heckeIntervalLogFactor_smooth :
    ContDiff ℝ ∞ (Function.uncurry heckeIntervalLogFactor) := by
  unfold heckeIntervalLogFactor Function.uncurry
  exact (Real.contDiff_exp.comp (contDiff_fst.snd.neg.mul contDiff_snd)).smul
    ((Complex.ofRealCLM.contDiff.comp contDiff_fst.fst).mul
      (PrimeLogProfile.safeInverse_smooth.comp
        (contDiff_const.sub (contDiff_fst.fst.mul contDiff_snd))))

def heckeIntervalLogFamily (ε u v : ℝ) (p : ℝ×ℝ) (s : ℝ) : ℂ :=
  heckeIntervalLogFactor p s*heckeLogIntervalProfile ε u v (-s)

theorem heckeIntervalLogFamily_eq (ε u v : ℝ) (p : ℝ×ℝ) (s : ℝ) :
    heckeIntervalLogFamily ε u v p s =
      PrimeLogProfile.logFamily (heckeLogIntervalCutoff ε u v) p s := by
  rw [PrimeLogProfile.logFamily, heckeLogIntervalCutoff_exp]
  unfold heckeIntervalLogFamily heckeIntervalLogFactor
  simp only [Complex.real_smul]
  ring

theorem heckeIntervalLogFamily_smooth (ε u v : ℝ) (p : ℝ×ℝ) :
    ContDiff ℝ ∞ (heckeIntervalLogFamily ε u v p) := by
  exact (heckeIntervalLogFactor_smooth.comp (contDiff_const.prodMk contDiff_id)).mul
    ((heckeLogIntervalProfile_smooth ε u v).comp contDiff_id.neg)

theorem heckeIntervalLogFamily_hasCompactSupport {ε u v : ℝ}
    (hε : 0 < ε) (huv : u ≤ v) (p : ℝ×ℝ) :
    HasCompactSupport (heckeIntervalLogFamily ε u v p) := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-(v+ε)) (-u)) isCompact_Icc
  intro s hs
  have hp : heckeLogIntervalProfile ε u v (-s) ≠ 0 := by
    intro h
    exact hs (by simp only [heckeIntervalLogFamily, h, mul_zero])
  have h := heckeLogIntervalProfile_support hε huv hp
  exact ⟨by linarith [h.2], by linarith [h.1]⟩

theorem heckeInterval_mellin_derivative_bound {ε u v : ℝ}
    (hε : 0 < ε) (huv : u ≤ v) (L σ t : ℝ) (j : ℕ) :
    (1+|t|)^j*‖mellin (PrimeLogProfile.profile (heckeLogIntervalCutoff ε u v) L)
      ((σ : ℂ)+(t : ℂ)*Complex.I)‖ ≤
      (1+2*Real.pi)^j*(2 : ℝ)^j*
      ((∫ s : ℝ, ‖heckeIntervalLogFamily ε u v (L,σ) s‖) +
        (∫ s : ℝ, ‖iteratedDeriv j (heckeIntervalLogFamily ε u v (L,σ)) s‖)/(2*Real.pi)^j) := by
  rw [CubicReflectionKernel.mellin_eq_logFamily_fourier]
  have he : CubicReflectionKernel.mellinLogFamily
      (PrimeLogProfile.profile (heckeLogIntervalCutoff ε u v) L) σ =
      heckeIntervalLogFamily ε u v (L,σ) := by
    funext s
    rw [heckeIntervalLogFamily_eq, PrimeLogProfile.logFamily_eq]
  rw [he]
  have hb := heckeFourier_weighted_derivative_bound (heckeIntervalLogFamily ε u v (L,σ))
    (heckeIntervalLogFamily_smooth ε u v (L,σ))
    (heckeIntervalLogFamily_hasCompactSupport hε huv (L,σ)) j (t/(2*Real.pi))
  have ht : |t| = (2*Real.pi)*|t/(2*Real.pi)| := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2*Real.pi)]
    field_simp
  have hbase : 1+|t| ≤ (1+2*Real.pi)*(1+|t/(2*Real.pi)|) := by
    rw [ht]
    nlinarith [Real.pi_pos, abs_nonneg (t/(2*Real.pi))]
  calc
    _ ≤ ((1+2*Real.pi)*(1+|t/(2*Real.pi)|))^j*
        ‖𝓕 (heckeIntervalLogFamily ε u v (L,σ)) (t/(2*Real.pi))‖ := by gcongr
    _ = (1+2*Real.pi)^j*((1+|t/(2*Real.pi)|)^j*
        ‖𝓕 (heckeIntervalLogFamily ε u v (L,σ)) (t/(2*Real.pi))‖) := by rw [mul_pow, mul_assoc]
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ (1+2*Real.pi)^j)

end ArtinMatthews
