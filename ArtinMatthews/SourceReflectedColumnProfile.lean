module

public import ArtinMatthews.SourceReflectedColumnDyad
public import ArtinMatthews.SourceReflectedLogProfile


set_option backward.privateInPublic true
@[expose] public section

/-! The one-column-dyad profile estimate with its Fourier coefficients
constructed and integrated. This consumes the smooth sheet bounds. -/
namespace ArtinMatthews.SourceReflection

open MeasureTheory
open scoped BigOperators ContDiff
noncomputable section

theorem sourceReflectedTwoEnded_le_one {α A u : ℝ} (hα : 0 ≤ α) (hA : 0 ≤ A) (hu : 0 < u) :
    min (u ^ α) (u ^ (-A)) ≤ 1 := by
  rcases le_total u 1 with h | h
  · exact (min_le_left _ _).trans (Real.rpow_le_one hu.le h hα)
  · exact (min_le_right _ _).trans (Real.rpow_le_one_of_one_le_of_nonpos h (neg_nonpos.mpr hA))

/-- The literal dyad profile enters with only the two-ended L¹ cost.
The constant is fixed before the profile, the dyad and the matrix data. -/
theorem sourceReflectedColumnDyadProfileEnergy {α A M : ℝ} (hα : 0 ≤ α) (hA : 0 ≤ A) (hM : 0 ≤ M)
    {Rows Cols : Type*} [Fintype Rows] [Fintype Cols] :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (Φ : ℝ → ℂ),
      ContDiff ℝ ∞ (fun s : ℝ => Φ (Real.exp s)) →
      (∀ i ≤ 2, ∀ s : ℝ, ‖iteratedFDeriv ℝ i (fun t : ℝ => Φ (Real.exp t)) s‖ ≤
        M * min (Real.exp (α * s)) (Real.exp (-A * s))) →
      ∀ (K : Rows → Cols → ℂ) (U : ℝ), 0 ≤ U →
      (∀ b : Cols → ℂ, (∑ i, ‖∑ j, K i j * b j‖ ^ 2) ≤ U ^ 2 * ∑ j, ‖b j‖ ^ 2) →
      ∀ (r : Rows → ℂ), (∀ i, ‖r i‖ ≤ 1) → ∀ (a : Cols → ℂ) (keep : Cols → Prop)
      [DecidablePred keep] (Ω D C : ℝ), 0 < Ω → 0 < D → 0 < C →
      ∀ (qR : Rows → ℝ) (qC : Cols → ℝ),
      (∀ i, D ≤ qR i ∧ qR i < 2 * D) → (∀ j, C ≤ qC j ∧ qC j < 2 * C) →
      Real.sqrt (∑ i, ‖∑ j, r i * K i j * (if keep j then a j else 0) *
        Φ (Ω * qC j / (qR i) ^ 2)‖ ^ 2) ≤
      C₀ * min ((Ω * C / D ^ 2) ^ α) ((Ω * C / D ^ 2) ^ (-A)) * U *
        Real.sqrt (∑ j, ‖if keep j then a j else 0‖ ^ 2) := by
  obtain ⟨C₀, hC₀, hcut⟩ := sourceReflectedLogFourier_exists hα hA hM
  refine ⟨C₀, hC₀, ?_⟩
  intro Φ hΦ hd K U hU hK r hr a keep _ Ω D C hΩ hD hC qR qC hR hQ
  let v₀ := Ω * C / D ^ 2
  have hv₀ : 0 < v₀ := div_pos (mul_pos hΩ hC) (sq_pos_of_pos hD)
  let g := sourceReflectedFourierCoefficient (sourceReflectedLogProfile Φ hΦ v₀)
  obtain ⟨hg, hinv, hL1⟩ := hcut Φ hΦ hd v₀ hv₀
  have h := source_fourier_separated_column_dyad_energy K hU hK r hr a keep Ω hD hC
    qR qC hR hQ Φ g hg hinv
  exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL1 hU) (Real.sqrt_nonneg _))

end
end ArtinMatthews.SourceReflection
