module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import Mathlib.Analysis.Normed.Ring.InfiniteSum


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute Taylor reindexing for the actual holomorphic Weyl orbital
series. Each periodized power then has its literal Lipschitz expansion. -/

noncomputable section
open UpperHalfPlane

namespace ArtinMatthews

def spectralPeterssonPeriodizedExponential (k : ℕ) (α : ℂ) (z : UpperHalfPlane) : ℂ :=
  ∑' l : ℤ, Complex.exp (α/((z : ℂ)+(l : ℂ)))/((z : ℂ)+(l : ℂ))^k

private theorem spectralPeterssonLinear_abs_summable (k : ℕ) (hk : 2 ≤ k)
    (z : UpperHalfPlane) :
    Summable (fun l : ℤ => (‖(z : ℂ)+(l : ℂ)‖^k)⁻¹) := by
  have h : (2 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  simpa only [Int.cast_one,one_mul,zpow_natCast,norm_inv,norm_pow] using
    (EisensteinSeries.linear_right_summable (z : ℂ) 1 h).norm

theorem spectralPeterssonPeriodizedExponential_taylor (k : ℕ) (hk : 2 ≤ k)
    (α : ℂ) (z : UpperHalfPlane) :
    spectralPeterssonPeriodizedExponential k α z =
      ∑' j : ℕ, α^j/(j.factorial : ℂ)*(∑' l : ℤ, (((z : ℂ)+(l : ℂ))^(k+j))⁻¹) := by
  let T (l : ℤ) (j : ℕ) : ℂ := α^j/(j.factorial : ℂ)*(((z : ℂ)+(l : ℂ))^(k+j))⁻¹
  let a (l : ℤ) : ℝ := (‖(z : ℂ)+(l : ℂ)‖^k)⁻¹
  let b (j : ℕ) : ℝ := (‖α‖/z.im)^j/(j.factorial : ℝ)
  have ha : Summable a := spectralPeterssonLinear_abs_summable k hk z
  have hb : Summable b := Real.summable_pow_div_factorial _
  have hab : Summable (fun p : ℤ × ℕ => a p.1*b p.2) :=
    Summable.mul_of_nonneg ha hb (fun l => by dsimp only [a]; positivity)
      (fun j => by dsimp only [b]; positivity)
  have hpoint (l : ℤ) (j : ℕ) : ‖T l j‖ ≤ a l*b j := by
    let u := ‖(z : ℂ)+(l : ℂ)‖
    have hu : z.im ≤ u := by
      simpa [u,abs_of_pos z.im_pos] using (Complex.abs_im_le_norm ((z : ℂ)+(l : ℂ)))
    have hratio : ‖α‖/u ≤ ‖α‖/z.im :=
      div_le_div_of_nonneg_left (norm_nonneg _) z.im_pos hu
    change ‖α^j/(j.factorial : ℂ)*(((z : ℂ)+(l : ℂ))^(k+j))⁻¹‖ ≤ a l*b j
    rw [norm_mul,norm_div,norm_pow,Complex.norm_natCast,norm_inv,norm_pow]
    change ‖α‖^j/(j.factorial : ℝ)*(u^(k+j))⁻¹ ≤ (u^k)⁻¹*((‖α‖/z.im)^j/(j.factorial : ℝ))
    calc
      _ = (u^k)⁻¹*((‖α‖/u)^j/(j.factorial : ℝ)) := by
        rw [pow_add,mul_inv_rev,div_pow]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (div_nonneg (norm_nonneg _) (norm_nonneg _)) hratio j) (Nat.cast_nonneg _))
        (inv_nonneg.mpr (pow_nonneg (norm_nonneg _) _))
  have hnorm : Summable (fun p : ℤ × ℕ => ‖T p.1 p.2‖) :=
    Summable.of_nonneg_of_le (g := fun p : ℤ × ℕ => ‖T p.1 p.2‖)
      (f := fun p : ℤ × ℕ => a p.1*b p.2) (fun p => norm_nonneg (T p.1 p.2))
      (fun p => hpoint p.1 p.2) hab
  have hs : Summable (Function.uncurry T) := hnorm.of_norm
  unfold spectralPeterssonPeriodizedExponential
  calc
    _ = ∑' l : ℤ, ∑' j : ℕ, T l j := by
      apply tsum_congr
      intro l
      let u := (z : ℂ)+(l : ℂ)
      change Complex.exp (α/u)/u^k = ∑' j : ℕ, T l j
      have he : Complex.exp (α/u) = ∑' j : ℕ, (α/u)^j/(j.factorial : ℂ) := by
        rw [Complex.exp_eq_exp_ℂ,NormedSpace.exp_eq_tsum_div]
      rw [he,div_eq_mul_inv,← tsum_mul_right]
      apply tsum_congr
      intro j
      change (α/u)^j/(j.factorial : ℂ)*(u^k)⁻¹ =
        α^j/(j.factorial : ℂ)*(u^(k+j))⁻¹
      rw [div_pow,pow_add,mul_inv_rev]
      ring
    _ = ∑' j : ℕ, ∑' l : ℤ, T l j := hs.tsum_comm.symm
    _ = _ := by
      apply tsum_congr
      intro j
      exact tsum_mul_left

theorem spectralPeterssonPeriodizedExponential_lipschitz (k : ℕ) (hk : 2 ≤ k)
    (α : ℂ) (z : UpperHalfPlane) :
    spectralPeterssonPeriodizedExponential k α z =
      ∑' j : ℕ, α^j/(j.factorial : ℂ)*
        ((-2*(Real.pi : ℂ)*Complex.I)^(k+j)/((k+j-1).factorial : ℂ))*
        (∑' n : ℕ+, (n : ℂ)^(k+j-1)*Complex.exp (2*(Real.pi : ℂ)*Complex.I*(z : ℂ))^(n : ℕ)) := by
  rw [spectralPeterssonPeriodizedExponential_taylor k hk α z]
  apply tsum_congr
  intro j
  have h := EisensteinSeries.qExpansion_identity_pnat (show 1 ≤ k+j-1 by omega) z
  rw [Nat.sub_add_cancel (show 1 ≤ k+j by omega)] at h
  simp only [one_div] at h
  rw [h]
  exact (mul_assoc _ _ _).symm

end ArtinMatthews
