module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
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

/-! Exact affine sublevel volumes used by the normalized moving box faces.
The lower slope is derived from the positive physical first-coordinate box. -/

noncomputable section
namespace ArtinMatthews
open MeasureTheory

theorem markedRoot_affine_strip_eq {a b c ε : ℝ} (ha : 0 < a) :
    {x : ℝ | |a*x+b-c| ≤ ε} = Set.Icc ((c-b-ε)/a) ((c-b+ε)/a) := by
  ext x
  rw [Set.mem_ofPred_eq,abs_le,Set.mem_Icc,div_le_iff₀ ha,le_div_iff₀ ha]
  constructor <;> intro h <;> constructor <;> nlinarith [h.1,h.2]

theorem markedRoot_affine_strip_volume {a b c ε : ℝ} (ha : 0 < a) :
    volume {x : ℝ | |a*x+b-c| ≤ ε} = ENNReal.ofReal (2*ε/a) := by
  rw [markedRoot_affine_strip_eq ha,Real.volume_Icc]
  congr 1
  ring

theorem markedRoot_affine_strip_volume_le {a b c ε : ℝ}
    (ha : (1/32:ℝ) ≤ a) (hε : 0 ≤ ε) :
    volume {x : ℝ | |a*x+b-c| ≤ ε} ≤ ENNReal.ofReal (64*ε) := by
  have hap : 0 < a := lt_of_lt_of_le (by norm_num) ha
  rw [markedRoot_affine_strip_volume hap]
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ hap).mpr
  nlinarith

theorem markedRoot_first_face_slope {a τ c ε : ℝ}
    (ha : a ∈ Set.Icc (1:ℝ) 16) (hc : 1 ≤ c) (hε : ε ≤ 1/2)
    (hx : |a*τ-c| ≤ ε) : (1/32:ℝ) ≤ τ := by
  have ht : 0 < τ := by
    by_contra h
    have hτ : τ ≤ 0 := le_of_not_gt h
    have ha0 : 0 ≤ a := by linarith [ha.1]
    nlinarith [(abs_le.mp hx).1,mul_nonpos_of_nonneg_of_nonpos ha0 hτ]
  have hmul := mul_le_mul_of_nonneg_right ha.2 ht.le
  nlinarith [(abs_le.mp hx).1]

theorem markedRoot_first_box_slope {a τ : ℝ}
    (ha : a ∈ Set.Icc (1:ℝ) 16) (hx : (1/2:ℝ) ≤ a*τ) : (1/32:ℝ) ≤ τ := by
  have ht : 0 < τ := by
    by_contra h
    have hτ : τ ≤ 0 := le_of_not_gt h
    have ha0 : 0 ≤ a := by linarith [ha.1]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos ha0 hτ]
  have hmul := mul_le_mul_of_nonneg_right ha.2 ht.le
  nlinarith

theorem markedRoot_first_face_slice {τ c ε : ℝ}
    (hc : 1 ≤ c) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1/2) :
    (volume.restrict (Set.Icc (1:ℝ) 16)) {a : ℝ | |a*τ-c| ≤ ε} ≤
      ENNReal.ofReal (64*ε) := by
  classical
  by_cases h : ∃ a ∈ Set.Icc (1:ℝ) 16,|a*τ-c| ≤ ε
  · obtain ⟨a,ha,hx⟩ := h
    have hτ := markedRoot_first_face_slope ha hc hε₁ hx
    apply (Measure.restrict_apply_le _ _).trans
    simpa only [mul_comm,add_zero] using markedRoot_affine_strip_volume_le (b := 0) (c := c) hτ hε₀
  · have he : {a : ℝ | |a*τ-c| ≤ ε} ∩ Set.Icc (1:ℝ) 16 = ∅ := by
      ext a
      simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
      exact fun ha => h ⟨a,ha.2,ha.1⟩
    rw [Measure.restrict_apply (by measurability),he,measure_empty]
    positivity

end ArtinMatthews
