module

public import ArtinMatthews.SourceThetaBesselMellin


set_option backward.privateInPublic true
@[expose] public section

/-! Positive real constants in the actual Bessel Mellin symbol. -/
namespace ArtinMatthews.SourceReflection

open Complex
open scoped Classical
noncomputable section

def sourceThetaArchConstant (c : ℝ) : ℝ :=
  2 * Real.pi * (2 / c ^ 2)

def sourceThetaArchScale (c : ℝ) : ℝ := (2 / c) ^ 2

theorem sourceThetaArchConstant_pos {c : ℝ} (hc : 0 < c) :
    0 < sourceThetaArchConstant c := by
  unfold sourceThetaArchConstant
  positivity

theorem sourceThetaArchScale_pos {c : ℝ} (hc : 0 < c) : 0 < sourceThetaArchScale c := by
  unfold sourceThetaArchScale
  positivity

theorem sourceThetaArchMellin_factor {c : ℝ} (hc : 0 < c) (s : ℂ) :
    ((2 * Real.pi : ℝ) : ℂ) *
        ((2 : ℂ) ^ (2 * s + 1) * (c : ℂ) ^ (-2 * s - 2) *
          Gamma (s + 5 / 6) * Gamma (s + 7 / 6)) =
      (sourceThetaArchConstant c : ℂ) * (sourceThetaArchScale c : ℂ) ^ s *
        (Gamma (s + 5 / 6) * Gamma (s + 7 / 6)) := by
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hlog : Complex.log 2 = (Real.log 2 : ℂ) := by
    simpa only [Complex.ofReal_ofNat] using
      (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  have hp : (2 : ℂ) ^ (2 * s) * (c : ℂ) ^ (-(2 * s)) =
      (sourceThetaArchScale c : ℂ) ^ s := by
    rw [Complex.cpow_def_of_ne_zero htwo, Complex.cpow_def_of_ne_zero hc',
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (sourceThetaArchScale_pos hc).ne'),
      ← Complex.exp_add, sourceThetaArchScale, hlog,
      ← Complex.ofReal_log hc.le, ← Complex.ofReal_log (sq_nonneg _),
      Real.log_pow, Real.log_div (by norm_num) hc.ne']
    congr 1
    push_cast
    ring
  rw [Complex.cpow_add _ _ htwo, Complex.cpow_one,
    show (-2 * s - 2 : ℂ) = -(2 * s) + -(2 : ℕ) by ring,
    Complex.cpow_add _ _ hc', Complex.cpow_neg (c : ℂ) (2 : ℕ), Complex.cpow_natCast]
  simp only [sourceThetaArchConstant, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_ofNat]
  rw [div_eq_mul_inv]
  rw [← hp]
  ring

/-- Products of positive real bases carry no branch correction. -/
theorem sourceThetaFinsetProd_cpow {ι : Type*} (T : Finset ι) (a : ι → ℝ) (s : ℂ)
    (ha : ∀ i ∈ T, 0 ≤ a i) :
    ((∏ i ∈ T, a i : ℝ) : ℂ) ^ s = ∏ i ∈ T, (a i : ℂ) ^ s := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert i T hi ih =>
    have hT (j : ι) (hj : j ∈ T) : 0 ≤ a j := ha j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (ha i (Finset.mem_insert_self _ _))
        (Finset.prod_nonneg hT), ih hT]

end
end ArtinMatthews.SourceReflection
