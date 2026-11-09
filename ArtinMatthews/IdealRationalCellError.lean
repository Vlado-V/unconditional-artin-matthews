module

public import ArtinMatthews.IdealRationalCellIdentity


set_option backward.privateInPublic true
@[expose] public section

/-! The retained rational phase error follows from actual primitive
reproduction, retaining the finite Gauss coefficient mass. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem idealTwoProduct_error {z w u v : ℂ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hu : ‖u-z‖ ≤ δ) (hv : ‖v-w‖ ≤ δ) :
    ‖z*w-u*v‖ ≤ δ*(2+δ) := by
  have hu' : ‖u‖ ≤ 1+δ := by
    calc
      _ = ‖(u-z)+z‖ := by ring_nf
      _ ≤ ‖u-z‖+‖z‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  calc
    _ = ‖(z-u)*w + u*(w-v)‖ := by congr 1; ring
    _ ≤ ‖(z-u)*w‖ + ‖u*(w-v)‖ := norm_add_le _ _
    _ = ‖z-u‖*‖w‖ + ‖u‖*‖w-v‖ := by rw [norm_mul, norm_mul]
    _ ≤ δ*1 + (1+δ)*δ := add_le_add
      (mul_le_mul (by simpa only [norm_sub_rev] using hu) hw (norm_nonneg _) hδ)
      (mul_le_mul hu' (by simpa only [norm_sub_rev] using hv) (norm_nonneg _) (by linarith))
    _ = _ := by ring

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

theorem idealRationalCellAverage_error (P : A → Finset ℕ) (R : B → Finset ℕ)
    {Q r : ℕ} [NeZero r] (hQr : r ≤ Q) (h ξ : ℝ) (u : ℤ)
    (hP : ∀ d : IdealSelectedLabels P, (idealSelectedProduct d).Coprime r)
    (hR : ∀ e : IdealSelectedLabels R, (idealSelectedProduct e).Coprime r)
    (x : IdealSelectedLabels P) (y : IdealSelectedLabels R) {δ : ℝ} (hδ : 0 ≤ δ)
    (hx : ∀ ψ : IdealPrimitiveCharacters Q,
      ‖idealCharacterCellApply P Q h ξ
          (fun d => idealPrimitiveCharacterValue ψ (idealSelectedProduct d)) x -
        idealPrimitiveCharacterValue ψ (idealSelectedProduct x)‖ ≤ δ)
    (hy : ∀ ψ : IdealPrimitiveCharacters Q,
      ‖idealCharacterCellApply R Q h ξ
          (fun e => idealPrimitiveCharacterValue ψ (idealSelectedProduct e)) y -
        idealPrimitiveCharacterValue ψ (idealSelectedProduct y)‖ ≤ δ) :
    ‖(Real.fourierChar ((u : ℝ)*(idealSelectedProduct x : ℝ)*(idealSelectedProduct y : ℝ)/r) : ℂ) -
      idealRationalCellAverage P R Q r h ξ u x y‖ ≤ Real.sqrt (r.totient : ℝ) * (δ*(2+δ)) := by
  rw [rationalPhase_bilinear_primitive_sum hQr u _ _ (hP x) (hR y),
    idealRationalCellAverage_eq P R hQr h ξ u hP hR x y, ← sum_sub_distrib]
  calc
    _ ≤ ∑ ψ : IdealPrimitiveCharacters Q,
        ‖rationalPhasePrimitiveCoefficient hQr u ψ *
          idealPrimitiveCharacterValue ψ (idealSelectedProduct x) *
          idealPrimitiveCharacterValue ψ (idealSelectedProduct y) -
          rationalPhasePrimitiveCoefficient hQr u ψ *
            idealCharacterCellApply P Q h ξ
              (fun d => idealPrimitiveCharacterValue ψ (idealSelectedProduct d)) x *
            idealCharacterCellApply R Q h ξ
              (fun e => idealPrimitiveCharacterValue ψ (idealSelectedProduct e)) y‖ := norm_sum_le _ _
    _ ≤ ∑ ψ : IdealPrimitiveCharacters Q,
        ‖rationalPhasePrimitiveCoefficient hQr u ψ‖ * (δ*(2+δ)) := by
      apply sum_le_sum
      intro ψ _
      have hh := idealTwoProduct_error hδ
        (idealPrimitiveCharacterValue_norm_le ψ _) (idealPrimitiveCharacterValue_norm_le ψ _)
        (hx ψ) (hy ψ)
      calc
        _ = ‖rationalPhasePrimitiveCoefficient hQr u ψ‖ *
          ‖idealPrimitiveCharacterValue ψ (idealSelectedProduct x) *
              idealPrimitiveCharacterValue ψ (idealSelectedProduct y) -
            idealCharacterCellApply P Q h ξ
              (fun d => idealPrimitiveCharacterValue ψ (idealSelectedProduct d)) x *
            idealCharacterCellApply R Q h ξ
              (fun e => idealPrimitiveCharacterValue ψ (idealSelectedProduct e)) y‖ := by
          rw [← norm_mul]
          congr 1
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hh (norm_nonneg _)
    _ = (∑ ψ : IdealPrimitiveCharacters Q, ‖rationalPhasePrimitiveCoefficient hQr u ψ‖) *
        (δ*(2+δ)) := (sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (rationalPhasePrimitiveCoefficient_l1_le hQr u) (by positivity)

end
end ArtinMatthews
