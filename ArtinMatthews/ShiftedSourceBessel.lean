module

public import ArtinMatthews.ShiftedSourceNormalization


set_option backward.privateInPublic true
@[expose] public section

/-! The actual shifted-correlation source cutoffs satisfy the uniform Bessel
smoothness requirements at dual length q²/(mT). Source seminorms are discharged
from finitely many derivatives of g and the constructed fixed plateau. -/

noncomputable section
open Complex Real Set OAI
open scoped ContDiff

namespace ArtinMatthews

/-- Uniform denominator derivatives for the actual first source cutoff.
Only finitely many of the prescribed T-scale derivative bounds for g are used. -/
theorem shiftedSourceTest_bessel_denominator_bound (A J : ℕ) :
    ∃ (L : ℕ) (C : ℝ), 0 < C ∧
      ∀ (g : ℝ → ℂ), ContDiff ℝ ∞ g → ∀ (T m Cg : ℝ), 0 < T → 0 < m → 0 ≤ Cg →
        Function.support g ⊆ Icc T (2*T) → 1 ≤ m*T →
        (∀ n ≤ L, ∀ x : ℝ, ‖iteratedDeriv n g x‖ ≤ Cg/T^n) →
        ∀ (x q : ℝ), 0 < x → 0 < q → ∀ j ≤ J,
          (1+(m*T)*(x/q^2))^A * ‖LocalLogFourier.eulerDeriv
            (fun z ↦ weightOneBesselTransform (shiftedSourceTest g m) (x/z^2)) j q‖ ≤
              2^j*C*Cg*(m*T) := by
  obtain ⟨s,C,hC,hb⟩ := weightOneBesselTransform_denominator_source_bound A J
  refine ⟨s.sup Prod.snd,C*3^(s.sup Prod.fst),by positivity,?_⟩
  intro g hg T m Cg hT hm hCg hgs hscale hderiv x q hx hq j hj
  let W := shiftedSourceTranslate (normalizedSourceSchwartz g hg T hT hgs) (1/(m*T))
  have hs : s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ 3^(s.sup Prod.fst)*Cg := by
    apply Seminorm.finset_sup_apply_le (by positivity)
    intro p hp
    have hfirst : p.1 ≤ s.sup Prod.fst := Finset.le_sup hp
    have hsecond : p.2 ≤ s.sup Prod.snd := Finset.le_sup hp
    exact (shiftedSourceTest_normalized_seminorm g hg T m Cg hT hgs hscale p.1 p.2 hCg
      (hderiv p.2 hsecond)).trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hfirst) hCg)
  have hsource : shiftedSourceTest g m = fun t : ℝ ↦ W (t/(m*T)) := by
    funext t
    exact shiftedSourceTest_eq_normalized g hg T m hT hm hgs t
  rw [hsource]
  have hbound := hb W 3 (by norm_num)
    (shiftedSourceTest_normalized_support g hg T m hT hgs hscale)
    (m*T) x q (mul_pos hm hT) hx hq j hj
  apply hbound.trans
  have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ (2 : ℝ)^j*C*(m*T) by positivity)
  convert hh using 1
  ring

/-- Uniform denominator derivatives for the actual second cutoff. All source
seminorms come from the fixed constructed plateau, so no derivative hypothesis
on a second free weight remains. -/
theorem shiftedSourceMajorant_bessel_denominator_bound (A J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T m : ℝ), 0 < T → 0 < m → 1 ≤ m*T →
      ∀ (x q : ℝ), 0 < x → 0 < q → ∀ j ≤ J,
        (1+(m*T)*(x/q^2))^A * ‖LocalLogFourier.eulerDeriv
          (fun z ↦ weightOneBesselTransform (shiftedSourceMajorant m T) (x/z^2)) j q‖ ≤
            2^j*C*(m*T) := by
  obtain ⟨s,C,hC,hb⟩ := weightOneBesselTransform_denominator_source_bound A J
  let M : ℝ := ∑ p ∈ s, (7/2 : ℝ)^p.1 * SchwartzMap.seminorm ℝ 0 p.2 sourcePlateauSchwartz
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨C*(1+M),by positivity,?_⟩
  intro T m hT hm hscale x q hx hq j hj
  let W := shiftedSourceTranslate sourcePlateauSchwartz (1/(m*T))
  have hδ : 1/(m*T) ∈ Icc 0 1 := ⟨by positivity,(div_le_one (mul_pos hm hT)).mpr hscale⟩
  have hsupport : Function.support sourcePlateauSchwartz ⊆ Icc 0 (5/2) :=
    shiftedSourcePlateau_support.trans (by intro y hy; exact ⟨by linarith [hy.1],hy.2⟩)
  have hs : s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ 1+M := by
    apply Seminorm.finset_sup_apply_le (by positivity)
    intro p hp
    have ht := shiftedSourceTranslate_seminorm sourcePlateauSchwartz (5/2) (1/(m*T))
      (by norm_num) hsupport hδ p.1 p.2
    norm_num only [show (5/2 : ℝ)+1=7/2 by norm_num] at ht
    have hu : (7/2 : ℝ)^p.1 * SchwartzMap.seminorm ℝ 0 p.2 sourcePlateauSchwartz ≤ M := by
      dsimp [M]
      exact Finset.single_le_sum
        (f := fun p : ℕ × ℕ ↦ (7/2 : ℝ)^p.1 * SchwartzMap.seminorm ℝ 0 p.2 sourcePlateauSchwartz)
        (fun i _ ↦ by positivity) hp
    exact ht.trans (by linarith)
  have hsource : shiftedSourceMajorant m T = fun t : ℝ ↦ W (t/(m*T)) := by
    funext t
    exact shiftedSourceMajorant_eq_normalized m T t
  rw [hsource]
  have hbound := hb W (7/2) (by norm_num) (shiftedSourceMajorant_normalized_support m T hscale)
    (m*T) x q (mul_pos hm hT) hx hq j hj
  apply hbound.trans
  have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ (2 : ℝ)^j*C*(m*T) by positivity)
  convert hh using 1
  ring

end ArtinMatthews
