module

public import ArtinMatthews.SpectralEisensteinLogGeometry
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset


set_option backward.privateInPublic true
@[expose] public section

/-! Row-independent logarithmic derivative bounds at positive height. -/
noncomputable section
open Set
namespace ArtinMatthews

private theorem eisenstein_abs_sub_le (a b : ℝ) : |a-b| ≤ |a|+|b| := by
  simpa only [sub_eq_add_neg,abs_neg] using (abs_add_le a (-b))

theorem eisensteinRowQuadratic_c_ratio (c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0)
    (p : ℝ × ℝ) (hp : 0 < p.2) : c^2/eisensteinRowQuadratic c d p ≤ 1/p.2^2 := by
  have hq := eisensteinRowQuadratic_pos c d hcd p hp
  apply (div_le_div_iff₀ hq (sq_pos_of_pos hp)).mpr
  unfold eisensteinRowQuadratic
  nlinarith [sq_nonneg (c*p.1+d)]

theorem eisensteinRowQuadratic_horizontal_ratio (c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0)
    (p : ℝ × ℝ) (hp : 0 < p.2) : (c*p.1+d)^2/eisensteinRowQuadratic c d p ≤ 1 := by
  have hq := eisensteinRowQuadratic_pos c d hcd p hp
  apply (div_le_one hq).mpr
  unfold eisensteinRowQuadratic
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem eisensteinRowQuadratic_vertical_ratio (c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0)
    (p : ℝ × ℝ) (hp : 0 < p.2) : (c*p.2)^2/eisensteinRowQuadratic c d p ≤ 1 := by
  have hq := eisensteinRowQuadratic_pos c d hcd p hp
  apply (div_le_one hq).mpr
  unfold eisensteinRowQuadratic
  exact le_add_of_nonneg_left (sq_nonneg _)

theorem eisensteinRowQuadratic_mixed_ratio (c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0)
    (p : ℝ × ℝ) (hp : 0 < p.2) : |c*(c*p.1+d)*p.2|/eisensteinRowQuadratic c d p ≤ 1 := by
  have hq := eisensteinRowQuadratic_pos c d hcd p hp
  apply (div_le_one hq).mpr
  rw [abs_mul,abs_mul,abs_of_pos hp]
  unfold eisensteinRowQuadratic
  have hh := sq_nonneg (|c| * p.2-|c*p.1+d|)
  simp only [sub_sq,mul_pow,sq_abs] at hh
  nlinarith [mul_nonneg (mul_nonneg (abs_nonneg c) (abs_nonneg (c*p.1+d))) hp.le]

theorem eisensteinRowLogX_bound (c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0)
    (p : ℝ × ℝ) (hp : 0 < p.2) : |eisensteinRowLogX c d p| ≤ 2/p.2 := by
  have hq := eisensteinRowQuadratic_pos c d hcd p hp
  have hb := eisensteinRowQuadratic_mixed_ratio c d hcd p hp
  have hb' : |c*(c*p.1+d)*p.2| ≤ eisensteinRowQuadratic c d p := (div_le_one hq).mp hb
  rw [abs_mul,abs_mul,abs_of_pos hp] at hb'
  unfold eisensteinRowLogX
  rw [abs_div,abs_neg,abs_of_pos hq,abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  apply (div_le_div_iff₀ hq hp).mpr
  nlinarith

theorem eisensteinRowLogY_bound (c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0)
    (p : ℝ × ℝ) (hp : 0 < p.2) : |eisensteinRowLogY c d p| ≤ 3/p.2 := by
  have hq := eisensteinRowQuadratic_pos c d hcd p hp
  have hratio : (2*c^2*p.2)/eisensteinRowQuadratic c d p ≤ 2/p.2 := by
    apply (div_le_div_iff₀ hq hp).mpr
    unfold eisensteinRowQuadratic
    nlinarith [sq_nonneg (c*p.1+d)]
  calc
    _ ≤ |1/p.2|+|(2*c^2*p.2)/eisensteinRowQuadratic c d p| := by
      exact eisenstein_abs_sub_le _ _
    _ = 1/p.2+(2*c^2*p.2)/eisensteinRowQuadratic c d p := by
      rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
    _ ≤ 1/p.2+2/p.2 := add_le_add le_rfl hratio
    _ = 3/p.2 := by ring

theorem eisensteinRowLogXX_bound (c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0)
    (p : ℝ × ℝ) (hp : 0 < p.2) : |eisensteinRowLogXX c d p| ≤ 6/p.2^2 := by
  have hq := eisensteinRowQuadratic_pos c d hcd p hp
  have hc := eisensteinRowQuadratic_c_ratio c d hcd p hp
  have ha := eisensteinRowQuadratic_horizontal_ratio c d hcd p hp
  have hm : (c^2/eisensteinRowQuadratic c d p)*((c*p.1+d)^2/eisensteinRowQuadratic c d p) ≤ 1/p.2^2 :=
    (mul_le_of_le_one_right (by positivity) ha).trans hc
  have hm' : (4*c^2*(c*p.1+d)^2)/(eisensteinRowQuadratic c d p)^2 ≤ 4/p.2^2 := by
    convert mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ)≤4) using 1 <;> ring
  have hc' : (2*c^2)/eisensteinRowQuadratic c d p ≤ 2/p.2^2 := by
    convert mul_le_mul_of_nonneg_left hc (by norm_num : (0:ℝ)≤2) using 1 <;> ring
  calc
    _ ≤ |-(2*c^2)/eisensteinRowQuadratic c d p|+
        |(4*c^2*(c*p.1+d)^2)/(eisensteinRowQuadratic c d p)^2| := abs_add_le _ _
    _ = (2*c^2)/eisensteinRowQuadratic c d p+
        (4*c^2*(c*p.1+d)^2)/(eisensteinRowQuadratic c d p)^2 := by
      rw [abs_div,abs_neg,abs_of_nonneg (by positivity),abs_of_pos hq,
        abs_of_nonneg (by positivity)]
    _ ≤ 2/p.2^2+4/p.2^2 := add_le_add hc' hm'
    _ = 6/p.2^2 := by ring

theorem eisensteinRowLogXY_bound (c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0)
    (p : ℝ × ℝ) (hp : 0 < p.2) : |eisensteinRowLogXY c d p| ≤ 4/p.2^2 := by
  have hq := eisensteinRowQuadratic_pos c d hcd p hp
  have hc := eisensteinRowQuadratic_c_ratio c d hcd p hp
  have ha := eisensteinRowQuadratic_mixed_ratio c d hcd p hp
  have hm : (c^2/eisensteinRowQuadratic c d p)*(|c*(c*p.1+d)*p.2|/eisensteinRowQuadratic c d p) ≤ 1/p.2^2 :=
    (mul_le_of_le_one_right (by positivity) ha).trans hc
  have he : |eisensteinRowLogXY c d p| =
      4*((c^2/eisensteinRowQuadratic c d p)*(|c*(c*p.1+d)*p.2|/eisensteinRowQuadratic c d p)) := by
    unfold eisensteinRowLogXY
    rw [abs_div,abs_of_nonneg (sq_nonneg (eisensteinRowQuadratic c d p))]
    have hcube : |c|^3 = c^2*|c| := by rw [pow_succ,sq_abs]
    simp only [abs_mul,abs_pow]
    rw [show |(4:ℝ)| = 4 from by norm_num,hcube]
    ring
  rw [he]
  convert mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ)≤4) using 1
  ring

theorem eisensteinRowLogYY_bound (c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0)
    (p : ℝ × ℝ) (hp : 0 < p.2) : |eisensteinRowLogYY c d p| ≤ 7/p.2^2 := by
  have hq := eisensteinRowQuadratic_pos c d hcd p hp
  have hc := eisensteinRowQuadratic_c_ratio c d hcd p hp
  have ha := eisensteinRowQuadratic_vertical_ratio c d hcd p hp
  have hm : (c^2/eisensteinRowQuadratic c d p)*((c*p.2)^2/eisensteinRowQuadratic c d p) ≤ 1/p.2^2 :=
    (mul_le_of_le_one_right (by positivity) ha).trans hc
  have hm' : (4*c^4*p.2^2)/(eisensteinRowQuadratic c d p)^2 ≤ 4/p.2^2 := by
    convert mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ)≤4) using 1 <;> ring
  have hc' : (2*c^2)/eisensteinRowQuadratic c d p ≤ 2/p.2^2 := by
    convert mul_le_mul_of_nonneg_left hc (by norm_num : (0:ℝ)≤2) using 1 <;> ring
  calc
    _ ≤ |-(1/p.2^2)-(2*c^2)/eisensteinRowQuadratic c d p|+
      |(4*c^4*p.2^2)/(eisensteinRowQuadratic c d p)^2| := abs_add_le _ _
    _ ≤ |-(1/p.2^2)|+|(2*c^2)/eisensteinRowQuadratic c d p|+
      |(4*c^4*p.2^2)/(eisensteinRowQuadratic c d p)^2| :=
      add_le_add (eisenstein_abs_sub_le _ _) le_rfl
    _ = 1/p.2^2+(2*c^2)/eisensteinRowQuadratic c d p+
      (4*c^4*p.2^2)/(eisensteinRowQuadratic c d p)^2 := by
      rw [abs_neg,abs_of_nonneg (by positivity),abs_of_nonneg (by positivity),
        abs_of_nonneg (by positivity)]
    _ ≤ 1/p.2^2+2/p.2^2+4/p.2^2 := add_le_add (add_le_add le_rfl hc') hm'
    _ = 7/p.2^2 := by ring

end ArtinMatthews
