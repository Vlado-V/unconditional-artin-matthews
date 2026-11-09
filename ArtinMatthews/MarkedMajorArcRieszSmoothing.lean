module

public import ArtinMatthews.MarkedMajorArcPerron


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite-sum identities connecting the proved Perron triangles with
the concrete endpoint smoothing, and exact cancellation of a common residue. -/
namespace ArtinMatthews

open Finset
open scoped BigOperators

lemma marked_riesz_triangle {x : ℝ} (hx : 0 < x) (t : ℝ) :
    (markedRieszCutoff x t : ℂ) = markedMellinTriangle (t/x) := by
  unfold markedRieszCutoff markedMellinTriangle
  rw [← max_div_div_right hx.le,zero_div,sub_div,div_self hx.ne']

lemma marked_riesz_sum_enlarge (a : ℕ → ℂ) {x : ℝ} (hx : 0 < x)
    {N : ℕ} (hN : ⌊x⌋₊ ≤ N) :
    (∑ n ∈ Icc 1 N, a n*(markedRieszCutoff x n : ℂ)) =
      ∑ n ∈ Icc 1 ⌊x⌋₊, a n*markedMellinTriangle ((n:ℝ)/x) := by
  simp_rw [marked_riesz_triangle hx]
  symm
  apply sum_subset (Icc_subset_Icc_right hN)
  intro n hn hn'
  have hlo : 1 ≤ n := (mem_Icc.mp hn).1
  have hlarge : ⌊x⌋₊ < n := by
    by_contra! hh
    exact hn' (mem_Icc.mpr ⟨hlo,hh⟩)
  have hxn := Nat.lt_of_floor_lt hlarge
  have hdiv : 1 ≤ (n:ℝ)/x := (le_div_iff₀ hx).mpr (by simpa using hxn.le)
  simp [markedMellinTriangle,max_eq_right (by linarith : 1-(n:ℝ)/x ≤ 0)]

/-- The literal smoothed sum is precisely the difference of the two finite
Riesz sums used in the Mellin calculation. -/
theorem marked_smoothed_sum_riesz (a : ℕ → ℂ) {ε x : ℝ}
    (hε : 0 < ε) (hx : 0 < x) {N : ℕ} (hN : ⌊(1+ε)*x⌋₊ ≤ N) :
    (∑ n ∈ Icc 1 N, a n*(markedSmoothedStep ε x n : ℂ)) =
      ((1+ε:ℝ):ℂ)*(∑ n ∈ Icc 1 ⌊(1+ε)*x⌋₊,
        a n*markedMellinTriangle ((n:ℝ)/((1+ε)*x)))/(ε:ℂ) -
      (∑ n ∈ Icc 1 ⌊x⌋₊, a n*markedMellinTriangle ((n:ℝ)/x))/(ε:ℂ) := by
  have hx' : 0 < (1+ε)*x := by positivity
  have hsmall : ⌊x⌋₊ ≤ N :=
    (Nat.floor_mono (show x ≤ (1+ε)*x by nlinarith)).trans hN
  rw [← marked_riesz_sum_enlarge a hx' hN,← marked_riesz_sum_enlarge a hx hsmall]
  simp only [marked_smoothed_step_riesz hε hx,Complex.ofReal_div,
    Complex.ofReal_sub,Complex.ofReal_mul]
  calc
    _ = (∑ n ∈ Icc 1 N, (((1+ε:ℝ):ℂ)*(a n*(markedRieszCutoff ((1+ε)*x) n : ℂ)) -
        a n*(markedRieszCutoff x n : ℂ)))/(ε:ℂ) := by
      rw [sum_div]
      apply sum_congr rfl
      intro n hn
      ring
    _ = _ := by rw [sum_sub_distrib,← mul_sum]; ring

lemma marked_common_residue_smoothing_bound {R₁ R₀ F : ℂ} {ε E₁ E₀ : ℝ}
    (hε : 0 < ε) (h₁ : ‖R₁-F‖ ≤ E₁) (h₀ : ‖R₀-F‖ ≤ E₀) :
    ‖((1+ε:ℝ):ℂ)*R₁/(ε:ℂ)-R₀/(ε:ℂ)-F‖ ≤ ((1+ε)*E₁+E₀)/ε := by
  have hεC : (ε:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
  have he : ((1+ε:ℝ):ℂ)*R₁/(ε:ℂ)-R₀/(ε:ℂ)-F =
      (((1+ε:ℝ):ℂ)*(R₁-F)-(R₀-F))/(ε:ℂ) := by
    push_cast
    field_simp
    ring
  rw [he,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε]
  apply div_le_div_of_nonneg_right _ hε.le
  apply (norm_sub_le _ _).trans
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : 0<1+ε)]
  exact add_le_add (mul_le_mul_of_nonneg_left h₁ (by positivity)) h₀

end ArtinMatthews
