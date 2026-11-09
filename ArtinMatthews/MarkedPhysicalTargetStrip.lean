module

public import ArtinMatthews.MarkedPhysicalRootCoordinates


set_option backward.privateInPublic true
@[expose] public section

/-! Exact signed target strips in the real root coordinate. Empty strips
and the zero determinant coordinate are retained explicitly. -/

noncomputable section
namespace ArtinMatthews

def markedPhysicalStripLower (z : ℤ × ℤ) : ℝ :=
  min ((-16-(z.1 : ℝ))/(z.2 : ℝ)) ((16-(z.1 : ℝ))/(z.2 : ℝ))

def markedPhysicalStripUpper (z : ℤ × ℤ) : ℝ :=
  max ((-16-(z.1 : ℝ))/(z.2 : ℝ)) ((16-(z.1 : ℝ))/(z.2 : ℝ))

theorem markedPhysicalTargetStrip_nonzero (z : ℤ × ℤ) (hn : z.2 ≠ 0) (r : ℝ) :
    |markedMinorIntegerTau r z| ≤ 16 ↔
      r ∈ Set.Icc (markedPhysicalStripLower z) (markedPhysicalStripUpper z) := by
  have hnR : (z.2 : ℝ) ≠ 0 := by exact_mod_cast hn
  rcases lt_or_gt_of_ne hnR with hneg | hpos
  · have horder : (16-(z.1 : ℝ))/(z.2 : ℝ) ≤ (-16-(z.1 : ℝ))/(z.2 : ℝ) := by
      apply (div_le_iff_of_neg hneg).mpr
      rw [div_mul_cancel₀ _ hnR]
      linarith
    simp only [markedMinorIntegerTau, markedPhysicalStripLower, markedPhysicalStripUpper,
      min_eq_right horder, max_eq_left horder, Set.mem_Icc, abs_le,
      div_le_iff_of_neg hneg, le_div_iff_of_neg hneg]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  · have horder : (-16-(z.1 : ℝ))/(z.2 : ℝ) ≤ (16-(z.1 : ℝ))/(z.2 : ℝ) :=
      div_le_div_of_nonneg_right (by linarith) hpos.le
    simp only [markedMinorIntegerTau, markedPhysicalStripLower, markedPhysicalStripUpper,
      min_eq_left horder, max_eq_right horder, Set.mem_Icc, abs_le,
      div_le_iff₀ hpos, le_div_iff₀ hpos]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

def markedPhysicalStripGate (z : ℤ × ℤ) : Prop :=
  z.2 ≠ 0 ∨ |(z.1 : ℝ)| ≤ 16

def markedPhysicalStripArcLower (z : ℤ × ℤ) (α : ℝ) : ℝ :=
  if z.2 = 0 then α else max α (markedPhysicalStripLower z)

def markedPhysicalStripArcUpper (z : ℤ × ℤ) (β : ℝ) : ℝ :=
  if z.2 = 0 then β else min β (markedPhysicalStripUpper z)

def markedPhysicalStripArcActive (z : ℤ × ℤ) (α β : ℝ) : Prop :=
  markedPhysicalStripGate z ∧ markedPhysicalStripArcLower z α ≤ markedPhysicalStripArcUpper z β

/-- Intersecting an elementary bad-root interval with the target strip gives
one interval, with a separate exact flag for an empty intersection. -/
theorem markedPhysicalTargetStrip_intersection (z : ℤ × ℤ) (α β r : ℝ) :
    (r ∈ Set.Icc α β ∧ |markedMinorIntegerTau r z| ≤ 16) ↔
      markedPhysicalStripArcActive z α β ∧
        r ∈ Set.Icc (markedPhysicalStripArcLower z α) (markedPhysicalStripArcUpper z β) := by
  classical
  by_cases hn : z.2 = 0
  · simp only [markedMinorIntegerTau, Int.cast_zero, mul_zero, add_zero,
      markedPhysicalStripArcActive, markedPhysicalStripGate, ne_eq, hn, not_true_eq_false,
      false_or, markedPhysicalStripArcLower, markedPhysicalStripArcUpper, ite_true, Set.mem_Icc]
    constructor
    · rintro ⟨⟨ha,hb⟩,hz⟩
      exact ⟨⟨hz,ha.trans hb⟩,ha,hb⟩
    · rintro ⟨⟨hz,_⟩,ha,hb⟩
      exact ⟨⟨ha,hb⟩,hz⟩
  · rw [markedPhysicalTargetStrip_nonzero z hn]
    simp only [markedPhysicalStripArcActive, markedPhysicalStripGate, ne_eq, hn, not_false_eq_true, true_or,
      true_and, markedPhysicalStripArcLower, markedPhysicalStripArcUpper, ite_false, Set.mem_Icc]
    constructor
    · rintro ⟨⟨ha,hb⟩,hl,hu⟩
      have hL := max_le ha hl
      have hU := le_min hb hu
      exact ⟨hL.trans hU,hL,hU⟩
    · rintro ⟨_,hL,hU⟩
      exact ⟨⟨(le_max_left _ _).trans hL,hU.trans (min_le_left _ _)⟩,
        (le_max_right _ _).trans hL,hU.trans (min_le_right _ _)⟩

theorem markedPhysicalStripArc_bounds (z : ℤ × ℤ) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hactive : markedPhysicalStripArcActive z α β) :
    0 ≤ markedPhysicalStripArcLower z α ∧
      markedPhysicalStripArcLower z α ≤ markedPhysicalStripArcUpper z β ∧
      markedPhysicalStripArcUpper z β ≤ 1 := by
  refine ⟨?_,hactive.2,?_⟩
  · unfold markedPhysicalStripArcLower
    split_ifs
    · exact hα
    · exact hα.trans (le_max_left _ _)
  · unfold markedPhysicalStripArcUpper
    split_ifs
    · exact hβ
    · exact (min_le_left _ _).trans hβ

theorem markedPhysicalTargetStrip_first_bound (z : ℤ × ℤ) {r : ℝ}
    (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) (hz : |markedMinorIntegerTau r z| ≤ 16) :
    |(z.1 : ℝ)| ≤ 16+|(z.2 : ℝ)| := by
  have he : (z.1 : ℝ) = markedMinorIntegerTau r z-r*(z.2 : ℝ) := by
    unfold markedMinorIntegerTau
    ring
  rw [he]
  apply (abs_sub _ _).trans
  have hr : |r| ≤ 1 := by rw [abs_of_nonneg hr₀]; exact hr₁
  rw [abs_mul]
  exact add_le_add hz (mul_le_of_le_one_left (abs_nonneg _) hr)

end ArtinMatthews
