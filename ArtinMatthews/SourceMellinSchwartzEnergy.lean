module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
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


set_option backward.privateInPublic true
@[expose] public section

/-! The positive Fourier weight in local Mellin energy is bounded by
Schwartz derivative energies. A genuinely band-limited inverse Fourier
transform satisfies the required scaled derivative estimates. -/

namespace ArtinMatthews
open MeasureTheory Complex Real
open scoped FourierTransform SchwartzMap ContDiff
noncomputable section

/-- Iterated derivatives represented as actual Schwartz functions. -/
def sourceMellinSchwartzDerivative (g : 𝓢(ℝ, ℂ)) : ℕ → 𝓢(ℝ, ℂ)
  | 0 => g
  | k + 1 => SchwartzMap.derivCLM ℂ ℂ (sourceMellinSchwartzDerivative g k)

theorem sourceMellinSchwartzDerivative_coe (g : 𝓢(ℝ, ℂ)) (k : ℕ) :
    (sourceMellinSchwartzDerivative g k : ℝ → ℂ) = iteratedDeriv k (g : ℝ → ℂ) := by
  induction k with
  | zero => rw [sourceMellinSchwartzDerivative, iteratedDeriv_zero]
  | succ k ih =>
    funext x
    rw [sourceMellinSchwartzDerivative, SchwartzMap.derivCLM_apply, iteratedDeriv_succ, ih]

theorem sourceMellinSchwartz_norm_sq_integrable (g : 𝓢(ℝ, ℂ)) :
    Integrable (fun x => ‖g x‖ ^ 2) :=
  (memLp_two_iff_integrable_sq_norm g.continuous.aestronglyMeasurable).mp (g.memLp 2)

theorem sourceMellinSchwartz_derivative_fourier_norm_sq
    (g : 𝓢(ℝ, ℂ)) (k : ℕ) (t : ℝ) :
    ‖(𝓕 (sourceMellinSchwartzDerivative g k)) t‖ ^ 2 =
      (2 * Real.pi * |t|) ^ (2 * k) * ‖(𝓕 g) t‖ ^ 2 := by
  have hi (n : ℕ) (_ : n ≤ (⊤ : ℕ∞)) : Integrable (iteratedDeriv n (g : ℝ → ℂ)) := by
    rw [← sourceMellinSchwartzDerivative_coe]
    exact (sourceMellinSchwartzDerivative g n).integrable
  have h := congrFun (Real.fourier_iteratedDeriv (g.smooth (⊤ : ℕ∞)) hi
    (n := k) (by simp)) t
  rw [← sourceMellinSchwartzDerivative_coe, ← SchwartzMap.fourier_coe,
    ← SchwartzMap.fourier_coe] at h
  have hn : ‖(2 : ℂ) * Real.pi * Complex.I * (t : ℂ)‖ = 2 * Real.pi * |t| := by
    simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [h, smul_eq_mul, norm_mul, norm_pow, hn, mul_pow, ← pow_mul, Nat.mul_comm k 2]

private theorem one_add_pow_le (u : ℝ) (hu : 0 ≤ u) (j : ℕ) :
    (1 + u) ^ j ≤ (2 : ℝ) ^ j * (1 + u ^ (2 * j)) := by
  by_cases h : u ≤ 1
  · calc
      _ ≤ (2 : ℝ) ^ j := pow_le_pow_left₀ (by positivity) (by linarith) j
      _ ≤ _ := le_mul_of_one_le_right (by positivity)
        (le_add_of_nonneg_right (pow_nonneg hu _))
  · have h₁ : 1 ≤ u := (lt_of_not_ge h).le
    calc
      _ ≤ (2 * u) ^ j := pow_le_pow_left₀ (by positivity) (by linarith) j
      _ = (2 : ℝ) ^ j * u ^ j := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((pow_le_pow_right₀ h₁ (by omega : j ≤ 2 * j)).trans
          (le_add_of_nonneg_left zero_le_one)) (by positivity)

theorem sourceMellinSchwartz_weighted_fourier_energy
    (g : 𝓢(ℝ, ℂ)) {W : ℝ} (hW : 0 < W) (j : ℕ) :
    Integrable (fun t : ℝ => (1 + |t| / W) ^ j * ‖(𝓕 g) t‖ ^ 2) ∧
    (∫ t : ℝ, (1 + |t| / W) ^ j * ‖(𝓕 g) t‖ ^ 2) ≤
      (2 : ℝ) ^ j * ((∫ x, ‖g x‖ ^ 2) +
        ((2 * Real.pi * W)⁻¹) ^ (2 * j) *
          ∫ x, ‖iteratedDeriv j (g : ℝ → ℂ) x‖ ^ 2) := by
  let d := sourceMellinSchwartzDerivative g j
  let b := ((2 * Real.pi * W)⁻¹) ^ (2 * j)
  have hb : 0 ≤ b := by positivity
  let f (t : ℝ) := (1 + |t| / W) ^ j * ‖(𝓕 g) t‖ ^ 2
  let F (t : ℝ) := (2 : ℝ) ^ j * (‖(𝓕 g) t‖ ^ 2 + b * ‖(𝓕 d) t‖ ^ 2)
  have hi₁ := sourceMellinSchwartz_norm_sq_integrable (𝓕 g)
  have hi₂ := (sourceMellinSchwartz_norm_sq_integrable (𝓕 d)).const_mul b
  have hF : Integrable F := (hi₁.add hi₂).const_mul _
  have hf₀ (t : ℝ) : 0 ≤ f t := by dsimp [f]; positivity
  have hbound (t : ℝ) : f t ≤ F t := by
    have hbase : |t| / W = (2 * Real.pi * W)⁻¹ * (2 * Real.pi * |t|) := by
      field_simp [hW.ne', Real.pi_ne_zero]
    have hterm : (|t| / W) ^ (2 * j) * ‖(𝓕 g) t‖ ^ 2 = b * ‖(𝓕 d) t‖ ^ 2 := by
      rw [hbase, mul_pow]
      change _ = b * ‖(𝓕 (sourceMellinSchwartzDerivative g j)) t‖ ^ 2
      rw [sourceMellinSchwartz_derivative_fourier_norm_sq]
      simp only [b, mul_assoc]
    calc
      f t ≤ (2 : ℝ) ^ j * (1 + (|t| / W) ^ (2 * j)) * ‖(𝓕 g) t‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (one_add_pow_le _ (by positivity) _) (sq_nonneg _)
      _ = F t := by
        simp only [F, mul_assoc, add_mul, one_mul, hterm]
  have hfc : Continuous f :=
    ((continuous_const.add (continuous_abs.div_const W)).pow j).mul
      (((𝓕 g : 𝓢(ℝ, ℂ)).continuous.norm).pow 2)
  have hf : Integrable f := hF.mono' hfc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => by rw [Real.norm_of_nonneg (hf₀ t)]; exact hbound t)
  refine ⟨hf, (integral_mono hf hF hbound).trans_eq ?_⟩
  dsimp only [F]
  rw [integral_const_mul, integral_add hi₁ hi₂, integral_const_mul,
    SchwartzMap.integral_norm_sq_fourier, SchwartzMap.integral_norm_sq_fourier]
  simp only [d, b, sourceMellinSchwartzDerivative_coe]

theorem sourceMellinSchwartz_band_derivative_energy (q : 𝓢(ℝ, ℂ))
    {R : ℝ} (_hR : 0 ≤ R) (hq : ∀ t : ℝ, R < |t| → q t = 0) (k : ℕ) :
    (∫ x, ‖iteratedDeriv k ((𝓕⁻ q : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖ ^ 2) ≤
      (2 * Real.pi * R) ^ (2 * k) * ∫ t, ‖q t‖ ^ 2 := by
  let g : 𝓢(ℝ, ℂ) := 𝓕⁻ q
  let d := sourceMellinSchwartzDerivative g k
  let C := (2 * Real.pi * R) ^ (2 * k)
  have he : (𝓕 g : 𝓢(ℝ, ℂ)) = q := FourierTransform.fourier_fourierInv_eq q
  have hpoint (t : ℝ) : ‖(𝓕 d) t‖ ^ 2 ≤ C * ‖q t‖ ^ 2 := by
    change ‖(𝓕 (sourceMellinSchwartzDerivative g k)) t‖ ^ 2 ≤ _
    rw [sourceMellinSchwartz_derivative_fourier_norm_sq, he]
    by_cases ht : |t| ≤ R
    · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply pow_le_pow_left₀ (by positivity) _ _
      exact mul_le_mul_of_nonneg_left ht (by positivity)
    · rw [hq t (lt_of_not_ge ht), norm_zero]
      simp
  calc
    _ = ∫ x, ‖d x‖ ^ 2 := by simp only [d, g, sourceMellinSchwartzDerivative_coe]
    _ = ∫ t, ‖(𝓕 d) t‖ ^ 2 := (SchwartzMap.integral_norm_sq_fourier d).symm
    _ ≤ ∫ t, C * ‖q t‖ ^ 2 := integral_mono
      (sourceMellinSchwartz_norm_sq_integrable (𝓕 d))
      ((sourceMellinSchwartz_norm_sq_integrable q).const_mul C) hpoint
    _ = _ := integral_const_mul _ _

end
end ArtinMatthews
