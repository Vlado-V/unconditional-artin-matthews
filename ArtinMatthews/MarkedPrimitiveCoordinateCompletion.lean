module

public import ArtinMatthews.MarkedPhysicalCanonicalRoots
public import Mathlib.Algebra.Group.Int.Units


set_option backward.privateInPublic true
@[expose] public section

/-! Actual bounded integral determinant-one complements for every
primitive coordinate, including a zero or negative first coordinate. -/
namespace ArtinMatthews
noncomputable section

theorem markedPositiveCompletion_second_bound (u v c d : ℤ) (hu : 0<u)
    (hc : 0≤c) (hcu : c<u) (hdet : u*d-v*c=1) : |d|≤1+|v| := by
  have he : u*d=1+v*c := by linarith
  have hbound : u*|d|≤u*(1+|v|) := by
    calc
      _ = |u*d| := by rw [abs_mul,abs_of_pos hu]
      _ = |1+v*c| := congrArg abs he
      _ ≤ 1+|v| * c := by
        simpa only [abs_one,abs_mul,abs_of_nonneg hc] using abs_add_le (1:ℤ) (v*c)
      _ ≤ u+|v| * u := by
        have hmul := mul_le_mul_of_nonneg_left hcu.le (abs_nonneg v)
        have hup : 1≤u := hu
        linarith
      _ = _ := by ring
  exact (mul_le_mul_iff_of_pos_left hu).mp hbound

theorem markedPositivePrimitiveCompletion (u v : ℤ) (hu : 0<u) (hz : IsCoprime u v) :
    ∃ w : ℤ × ℤ,markedMinorIntegerDet (u,v) w=1 ∧ |w.1|≤|u| ∧ |w.2|≤1+|v| := by
  obtain ⟨c,d,hc,hcu,hd⟩ := markedPhysical_canonical_completion u v hu hz
  refine ⟨(c,d),hd,?_,markedPositiveCompletion_second_bound u v c d hu hc hcu hd⟩
  simpa only [abs_of_nonneg hc,abs_of_pos hu] using hcu.le

theorem markedPrimitiveCoordinateCompletion_exists (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) :
    ∃ w : ℤ × ℤ,markedMinorIntegerDet z w=1 ∧
      |w.1|≤1+|z.1| ∧ |w.2|≤1+|z.2| := by
  by_cases hzero : z.1=0
  · obtain ⟨a,b,hab⟩ := hz
    have hv : z.2*b=1 := by simpa only [hzero,mul_zero,zero_add,mul_comm] using hab
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hv with hv | hv <;>
      refine ⟨(-z.2,0),?_,?_,?_⟩ <;> simp [markedMinorIntegerDet,hzero,hv]
  · by_cases hu : 0<z.1
    · obtain ⟨w,hd,h₁,h₂⟩ := markedPositivePrimitiveCompletion z.1 z.2 hu hz
      exact ⟨w,hd,h₁.trans (by omega),h₂⟩
    · have hneg : IsCoprime (-z.1) (-z.2) := by
        obtain ⟨a,b,hab⟩ := hz
        refine ⟨-a,-b,?_⟩
        linear_combination hab
      obtain ⟨w,hd,h₁,h₂⟩ := markedPositivePrimitiveCompletion (-z.1) (-z.2) (by omega) hneg
      have hb₁ : |w.1|≤1+|z.1| := by simpa only [abs_neg] using h₁.trans (by omega : |-(z.1)|≤1+|-(z.1)|)
      have hb₂ : |w.2|≤1+|z.2| := by simpa only [abs_neg] using h₂
      refine ⟨(-w.1,-w.2),?_,by simpa only [abs_neg] using hb₁,by simpa only [abs_neg] using hb₂⟩
      calc
        _ = markedMinorIntegerDet (-z.1,-z.2) w := by unfold markedMinorIntegerDet; ring
        _ = 1 := hd

def markedPrimitiveCoordinateCompletion (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) : ℤ × ℤ :=
  (markedPrimitiveCoordinateCompletion_exists z hz).choose

theorem markedPrimitiveCoordinateCompletion_det (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) :
    markedMinorIntegerDet z (markedPrimitiveCoordinateCompletion z hz)=1 :=
  (markedPrimitiveCoordinateCompletion_exists z hz).choose_spec.1

theorem markedPrimitiveCoordinateCompletion_fst_bound (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) :
    |(markedPrimitiveCoordinateCompletion z hz).1|≤1+|z.1| :=
  (markedPrimitiveCoordinateCompletion_exists z hz).choose_spec.2.1

theorem markedPrimitiveCoordinateCompletion_snd_bound (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) :
    |(markedPrimitiveCoordinateCompletion z hz).2|≤1+|z.2| :=
  (markedPrimitiveCoordinateCompletion_exists z hz).choose_spec.2.2

theorem markedPrimitiveCoordinateCompletion_real_bound (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (H : ℝ) (h₁ : |(z.1:ℝ)|≤H) (h₂ : |(z.2:ℝ)|≤H) :
    |((markedPrimitiveCoordinateCompletion z hz).1:ℝ)|≤H+1 ∧
      |((markedPrimitiveCoordinateCompletion z hz).2:ℝ)|≤H+1 := by
  have hc₁ : |((markedPrimitiveCoordinateCompletion z hz).1:ℝ)|≤1+|(z.1:ℝ)| := by
    exact_mod_cast markedPrimitiveCoordinateCompletion_fst_bound z hz
  have hc₂ : |((markedPrimitiveCoordinateCompletion z hz).2:ℝ)|≤1+|(z.2:ℝ)| := by
    exact_mod_cast markedPrimitiveCoordinateCompletion_snd_bound z hz
  constructor <;> linarith

end
end ArtinMatthews
