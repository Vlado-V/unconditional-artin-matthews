module

public import ArtinMatthews.MarkedMinorArcSharedLattice
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Order.Floor.Ring


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine separation of primitive integer slopes. The upper bound on
the first coordinate is explicit, including the physical box factor 16. -/
namespace ArtinMatthews
open scoped Classical
noncomputable section

def markedPhysicalSlope (p : ℤ × ℤ) : ℝ := (p.2 : ℝ)/(p.1 : ℝ)

theorem markedPrimitive_det_zero_eq (p q : ℤ × ℤ)
    (hp : IsCoprime p.1 p.2) (hq : IsCoprime q.1 q.2)
    (hp1 : 0 < p.1) (hq1 : 0 < q.1) (hd : markedMinorIntegerDet p q = 0) : p = q := by
  have he : p.1*q.2 = p.2*q.1 := by
    simpa only [markedMinorIntegerDet,sub_eq_zero] using hd
  have hpq : p.1 ∣ q.1 := hp.dvd_of_dvd_mul_left (by
    rw [← he]
    exact dvd_mul_right _ _)
  have hqp : q.1 ∣ p.1 := hq.dvd_of_dvd_mul_left (by
    rw [mul_comm q.2 p.1,he,mul_comm p.2 q.1]
    exact dvd_mul_right _ _)
  have h1 : p.1=q.1 := le_antisymm (Int.le_of_dvd hq1 hpq) (Int.le_of_dvd hp1 hqp)
  have h2 : p.2=q.2 := by
    apply mul_left_cancel₀ hp1.ne'
    rw [← h1] at he
    exact (mul_comm p.1 p.2).trans he.symm
  exact Prod.ext h1 h2

theorem markedPrimitive_det_ne_zero (p q : ℤ × ℤ)
    (hp : IsCoprime p.1 p.2) (hq : IsCoprime q.1 q.2)
    (hp1 : 0 < p.1) (hq1 : 0 < q.1) (hpq : p ≠ q) : markedMinorIntegerDet p q ≠ 0 :=
  fun h => hpq (markedPrimitive_det_zero_eq p q hp hq hp1 hq1 h)

theorem markedPhysicalSlope_difference (p q : ℤ × ℤ) (hp1 : p.1 ≠ 0) (hq1 : q.1 ≠ 0) :
    markedPhysicalSlope q-markedPhysicalSlope p =
      (markedMinorIntegerDet p q : ℝ)/((p.1 : ℝ)*(q.1 : ℝ)) := by
  unfold markedPhysicalSlope markedMinorIntegerDet
  push_cast
  field_simp

theorem markedPrimitiveSlope_separated (p q : ℤ × ℤ)
    (hp : IsCoprime p.1 p.2) (hq : IsCoprime q.1 q.2)
    (hp1 : 0 < p.1) (hq1 : 0 < q.1) (hpq : p ≠ q)
    (A : ℝ) (hA : 0 < A) (hpA : (p.1 : ℝ) ≤ A) (hqA : (q.1 : ℝ) ≤ A) :
    1/A^2 ≤ |markedPhysicalSlope q-markedPhysicalSlope p| := by
  have hp1r : (0 : ℝ) < p.1 := by exact_mod_cast hp1
  have hq1r : (0 : ℝ) < q.1 := by exact_mod_cast hq1
  have hd := markedPrimitive_det_ne_zero p q hp hq hp1 hq1 hpq
  have hi : (1 : ℤ) ≤ |markedMinorIntegerDet p q| := by
    have hh := abs_pos.mpr hd
    omega
  have hir : (1 : ℝ) ≤ |(markedMinorIntegerDet p q : ℝ)| := by exact_mod_cast hi
  rw [markedPhysicalSlope_difference p q hp1.ne' hq1.ne',abs_div,abs_mul,
    abs_of_pos hp1r,abs_of_pos hq1r]
  calc
    _ ≤ 1/((p.1 : ℝ)*(q.1 : ℝ)) := by
      apply div_le_div_of_nonneg_left (by norm_num) (mul_pos hp1r hq1r)
      nlinarith [mul_le_mul hpA hqA hq1r.le hA.le]
    _ ≤ _ := div_le_div_of_nonneg_right hir (mul_pos hp1r hq1r).le

theorem markedPhysicalSlope_separated_box (p q : ℤ × ℤ)
    (hp : IsCoprime p.1 p.2) (hq : IsCoprime q.1 q.2) (hpq : p ≠ q)
    (U B : ℝ) (hU : 0 < U) (hB : 0 < B)
    (hpU : U ≤ (p.1 : ℝ)) (hqU : U ≤ (q.1 : ℝ))
    (hpB : (p.1 : ℝ) ≤ B*U) (hqB : (q.1 : ℝ) ≤ B*U) :
    1/(B^2*U^2) ≤ |markedPhysicalSlope q-markedPhysicalSlope p| := by
  have hp1 : 0 < p.1 := by exact_mod_cast (hU.trans_le hpU)
  have hq1 : 0 < q.1 := by exact_mod_cast (hU.trans_le hqU)
  simpa only [mul_pow] using
    markedPrimitiveSlope_separated p q hp hq hp1 hq1 hpq (B*U) (mul_pos hB hU) hpB hqB

end
end ArtinMatthews
