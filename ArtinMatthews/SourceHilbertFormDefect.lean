module

public import ArtinMatthews.SourceHilbertPencil
public import ArtinMatthews.SourceHilbertFredholmCriterion
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity


set_option backward.privateInPublic true
@[expose] public section

/-! A form estimate with a compact remainder gives a Fredholm Gram pencil. -/
namespace ArtinMatthews.HilbertResolvent

open scoped InnerProductSpace
noncomputable section

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (j : V →L[ℂ] H)

theorem pencil_adjoint_comp_selfAdjoint (center : ℝ) :
    IsSelfAdjoint (pencil (j.adjoint.comp j) (center : ℂ)) := by
  apply pencil_center_selfAdjoint
  simp [ContinuousLinearMap.isSelfAdjoint_iff']

theorem pencil_adjoint_comp_re_inner (center : ℝ) (u : V) :
    (inner ℂ u (pencil (j.adjoint.comp j) (center : ℂ) u)).re =
      ‖u‖ ^ 2 - (center + 1) * ‖j u‖ ^ 2 := by
  have h : inner ℂ u (pencil (j.adjoint.comp j) (center : ℂ) u) =
      ((‖u‖ ^ 2 - (center + 1) * ‖j u‖ ^ 2 : ℝ) : ℂ) := by
    change inner ℂ u (u - ((center : ℂ) + 1) • j.adjoint (j u)) = _
    simp only [inner_sub_right, inner_smul_right, j.adjoint_inner_right,
      inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
      Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_one,
      Complex.ofReal_pow]
  rw [h, Complex.ofReal_re]

variable {H₀ : Type*} [NormedAddCommGroup H₀] [NormedSpace ℂ H₀]
variable (K : V →L[ℂ] H₀)

theorem pencil_adjoint_comp_norm_estimate {r center C : ℝ}
    (hr : 0 ≤ r) (hcenter : center < r) (hC : 0 ≤ C)
    (hform : ∀ u : V, r * ‖j u‖ ^ 2 ≤ ‖u‖ ^ 2 - ‖j u‖ ^ 2 + C * ‖K u‖ ^ 2) :
    ∃ A D : ℝ, 0 < A ∧ 0 < D ∧ ∀ u : V,
      ‖u‖ ^ 2 ≤ A * ‖pencil (j.adjoint.comp j) (center : ℂ) u‖ ^ 2 + D * ‖K u‖ ^ 2 := by
  let scale := r + 1
  let t := max (center + 1) 0
  let gap := scale - t
  have hscale : 0 < scale := by dsimp [scale]; positivity
  have ht : 0 ≤ t := le_max_right _ _
  have ht_lt : t < scale := max_lt_iff.mpr ⟨by dsimp [scale]; linarith, hscale⟩
  have hgap : 0 < gap := sub_pos.mpr ht_lt
  let weight := (gap ^ 2)⁻¹
  have hweight : 0 < weight := inv_pos.mpr (pow_pos hgap 2)
  refine ⟨weight * scale ^ 2, weight * (2 * gap * t * C) + 1,
    mul_pos hweight (pow_pos hscale 2), ?_, ?_⟩
  · positivity
  intro u
  let B := pencil (j.adjoint.comp j) (center : ℂ)
  have hpencil : ‖u‖ ^ 2 - t * ‖j u‖ ^ 2 ≤ ‖u‖ * ‖B u‖ := calc
    _ ≤ ‖u‖ ^ 2 - (center + 1) * ‖j u‖ ^ 2 :=
      sub_le_sub_left (mul_le_mul_of_nonneg_right (le_max_left (center + 1) 0) (sq_nonneg _)) _
    _ = (inner ℂ u (B u)).re := (pencil_adjoint_comp_re_inner j center u).symm
    _ ≤ _ := re_inner_le_norm (𝕜 := ℂ) u (B u)
  have hmass : scale * ‖j u‖ ^ 2 - ‖u‖ ^ 2 ≤ C * ‖K u‖ ^ 2 := by
    dsimp [scale]
    nlinarith only [hform u]
  have hquadratic : gap * ‖u‖ ^ 2 ≤ scale * ‖u‖ * ‖B u‖ + t * C * ‖K u‖ ^ 2 := calc
    _ = scale * (‖u‖ ^ 2 - t * ‖j u‖ ^ 2) + t * (scale * ‖j u‖ ^ 2 - ‖u‖ ^ 2) := by
      dsimp [gap]
      ring
    _ ≤ scale * (‖u‖ * ‖B u‖) + t * (C * ‖K u‖ ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hpencil hscale.le) (mul_le_mul_of_nonneg_left hmass ht)
    _ = _ := by ring
  have hscaled := mul_le_mul_of_nonneg_left hquadratic (show 0 ≤ 2 * gap by positivity)
  have hsq : gap ^ 2 * ‖u‖ ^ 2 ≤ scale ^ 2 * ‖B u‖ ^ 2 + (2 * gap * t * C) * ‖K u‖ ^ 2 := by
    nlinarith only [hscaled, sq_nonneg (gap * ‖u‖ - scale * ‖B u‖)]
  calc
    ‖u‖ ^ 2 = weight * (gap ^ 2 * ‖u‖ ^ 2) := by
      dsimp only [weight]
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (pow_pos hgap 2)), one_mul]
    _ ≤ weight * (scale ^ 2 * ‖B u‖ ^ 2 + (2 * gap * t * C) * ‖K u‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsq hweight.le
    _ = (weight * scale ^ 2) * ‖B u‖ ^ 2 + (weight * (2 * gap * t * C)) * ‖K u‖ ^ 2 := by ring
    _ ≤ _ := add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (sq_nonneg _))

theorem pencil_adjoint_comp_fredholm_of_form_estimate (hK : IsCompactOperator K) {r center C : ℝ}
    (hr : 0 ≤ r) (hcenter : center < r) (hC : 0 ≤ C)
    (hform : ∀ u : V, r * ‖j u‖ ^ 2 ≤ ‖u‖ ^ 2 - ‖j u‖ ^ 2 + C * ‖K u‖ ^ 2) :
    (pencil (j.adjoint.comp j) (center : ℂ)).IsFredholm :=
  fredholm_of_compact_defect _ (pencil_adjoint_comp_selfAdjoint j center) K hK
    (pencil_adjoint_comp_norm_estimate j K hr hcenter hC hform)

end
end ArtinMatthews.HilbertResolvent
