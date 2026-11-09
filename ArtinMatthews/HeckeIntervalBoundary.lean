module

public import ArtinMatthews.HeckeIntervalCutoff
public import ArtinMatthews.MarkedMajorArcSmoothing


set_option backward.privateInPublic true
@[expose] public section

/-! The concrete logarithmic smoothing differs from a sharp interval only
in its two explicit transition strips. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators Classical

theorem heckeLogIntervalProfile_one {ε u v s : ℝ}
    (hε : 0 < ε) (hlo : u+ε ≤ s) (hhi : s ≤ v) :
    heckeLogIntervalProfile ε u v s = 1 := by
  unfold heckeLogIntervalProfile
  rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ hε).mpr (by linarith)),
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le)]
  simp

theorem heckeLogIntervalProfile_boundary {ε u v : ℝ}
    (hε : 0 < ε) (huv : u ≤ v) (s : ℝ) :
    ‖heckeLogIntervalProfile ε u v s-(if u<s ∧ s≤v then (1 : ℂ) else 0)‖ ≤
      2*((if u<s ∧ s<u+ε then (1 : ℝ) else 0) +
        (if v<s ∧ s<v+ε then (1 : ℝ) else 0)) := by
  have hb : ‖heckeLogIntervalProfile ε u v s-(if u<s ∧ s≤v then (1 : ℂ) else 0)‖ ≤ 2 := by
    apply (norm_sub_le _ _).trans
    have hi : ‖(if u<s ∧ s≤v then (1 : ℂ) else 0)‖ ≤ 1 := by split_ifs <;> norm_num
    linarith [heckeLogIntervalProfile_norm_le_one hε huv s]
  by_cases hl : u<s ∧ s<u+ε
  · apply hb.trans
    simp only [ite_eq_left hl]
    split_ifs <;> norm_num
  by_cases hr : v<s ∧ s<v+ε
  · apply hb.trans
    simp only [ite_eq_right hl, ite_eq_left hr]
    norm_num
  rw [ite_eq_right hl, ite_eq_right hr]
  by_cases hs : u<s
  · have hleft : u+ε ≤ s := by grind
    by_cases hright : s≤v
    · rw [heckeLogIntervalProfile_one hε hleft hright, ite_eq_left ⟨hs, hright⟩]
      norm_num
    · have hv : v+ε ≤ s := by grind
      rw [heckeLogIntervalProfile_zero_right hε huv hv, ite_eq_right (by simp [hright])]
      norm_num
  · rw [heckeLogIntervalProfile_zero_left hε huv (le_of_not_gt hs), ite_eq_right (by simp [hs])]
    norm_num

theorem heckeLogInterval_finite_boundary {ε u v H M : ℝ}
    (hε : 0 < ε) (huv : u ≤ v) (hH : 0 < H) (hM : 0 ≤ M)
    (S : Finset ℕ) (a : ℕ → ℂ) (hS : ∀ n ∈ S, 0 < n)
    (ha : ∀ n ∈ S, ‖a n‖ ≤ M) :
    ‖(∑ n ∈ S, a n*heckeLogIntervalCutoff ε u v ((n : ℝ)/H)) -
      (∑ n ∈ S, a n*(if u<Real.log ((n : ℝ)/H) ∧ Real.log ((n : ℝ)/H)≤v
        then (1 : ℂ) else 0))‖ ≤
      2*M*((S.filter (fun n : ℕ => u<Real.log ((n : ℝ)/H) ∧
        Real.log ((n : ℝ)/H)<u+ε)).card +
        (S.filter (fun n : ℕ => v<Real.log ((n : ℝ)/H) ∧
        Real.log ((n : ℝ)/H)<v+ε)).card : ℝ) := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ S, ‖a n*heckeLogIntervalCutoff ε u v ((n : ℝ)/H) -
      a n*(if u<Real.log ((n : ℝ)/H) ∧ Real.log ((n : ℝ)/H)≤v then (1 : ℂ) else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, 2*M*((if u<Real.log ((n : ℝ)/H) ∧
        Real.log ((n : ℝ)/H)<u+ε then (1 : ℝ) else 0) +
        (if v<Real.log ((n : ℝ)/H) ∧ Real.log ((n : ℝ)/H)<v+ε then (1 : ℝ) else 0)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : 0 < (n : ℝ)/H := div_pos (by exact_mod_cast hS n hn) hH
      rw [← mul_sub, norm_mul, heckeLogIntervalCutoff, ite_eq_left hnpos]
      calc
        _ ≤ M*(2*((if u<Real.log ((n : ℝ)/H) ∧ Real.log ((n : ℝ)/H)<u+ε then (1 : ℝ) else 0)+
          (if v<Real.log ((n : ℝ)/H) ∧ Real.log ((n : ℝ)/H)<v+ε then (1 : ℝ) else 0))) :=
          mul_le_mul (ha n hn) (heckeLogIntervalProfile_boundary hε huv _) (norm_nonneg _) hM
        _ = _ := by ring
    _ = _ := by simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_boole]

end ArtinMatthews
