module

public import ArtinMatthews.SourceReflectedFourierSeparation


set_option backward.privateInPublic true
@[expose] public section

/-! Literal source row and column dyad ratios. The retained cutoff is a
column factor after the two frozen ideals have been fixed. -/
namespace ArtinMatthews.SourceReflection

open MeasureTheory Set
open scoped BigOperators
noncomputable section

theorem sourceReflectedDyad_logRatio_mem {D C d c : ℝ} (hD : 0 < D) (hC : 0 < C)
    (hd : D ≤ d ∧ d < 2 * D) (hc : C ≤ c ∧ c < 2 * C) :
    -2 * Real.log (d / D) + Real.log (c / C) ∈ Icc (-(2 * Real.log 2)) (Real.log 2) := by
  have hd₁ : 1 ≤ d / D := (le_div_iff₀ hD).mpr (by simpa only [one_mul] using hd.1)
  have hc₁ : 1 ≤ c / C := (le_div_iff₀ hC).mpr (by simpa only [one_mul] using hc.1)
  have hd₂ : d / D ≤ 2 := (div_le_iff₀ hD).mpr hd.2.le
  have hc₂ : c / C ≤ 2 := (div_le_iff₀ hC).mpr hc.2.le
  have hlogd := Real.log_nonneg hd₁
  have hlogc := Real.log_nonneg hc₁
  have hlogd₂ := Real.log_le_log (zero_lt_one.trans_le hd₁) hd₂
  have hlogc₂ := Real.log_le_log (zero_lt_one.trans_le hc₁) hc₂
  exact ⟨by linarith, by linarith⟩

theorem sourceReflectedDyad_profileArgument (Ω : ℝ) {D C d c : ℝ}
    (hD : 0 < D) (hC : 0 < C) (hd : 0 < d) (hc : 0 < c) :
    (Ω * C / D ^ 2) * Real.exp (-2 * Real.log (d / D) + Real.log (c / C)) = Ω * c / d ^ 2 := by
  have hrow : Real.exp (-2 * Real.log (d / D)) = ((d / D) ^ 2)⁻¹ := by
    rw [show -2 * Real.log (d / D) = -(Real.log (d / D) + Real.log (d / D)) by ring,
      Real.exp_neg, Real.exp_add, Real.exp_log (div_pos hd hD), pow_two]
  rw [Real.exp_add, hrow, Real.exp_log (div_pos hc hC)]
  field_simp

/-- Exact one-column-dyad estimate. `keep` depends only on the column,
and the row and column log ratios are the ones used in the source. -/
theorem source_fourier_separated_column_dyad_energy {Rows Cols : Type*} [Fintype Rows] [Fintype Cols]
    (K : Rows → Cols → ℂ) {U : ℝ} (hU : 0 ≤ U)
    (hK : ∀ b : Cols → ℂ, (∑ i, ‖∑ j, K i j * b j‖ ^ 2) ≤ U ^ 2 * ∑ j, ‖b j‖ ^ 2)
    (r : Rows → ℂ) (hr : ∀ i, ‖r i‖ ≤ 1) (a : Cols → ℂ)
    (keep : Cols → Prop) [DecidablePred keep] (Ω : ℝ) {D C : ℝ} (hD : 0 < D) (hC : 0 < C)
    (qR : Rows → ℝ) (qC : Cols → ℝ) (hR : ∀ i, D ≤ qR i ∧ qR i < 2 * D)
    (hQ : ∀ j, C ≤ qC j ∧ qC j < 2 * C) (Φ : ℝ → ℂ) (g : ℝ → ℂ) (hg : Integrable g)
    (hInv : ∀ x ∈ Icc (-(2 * Real.log 2)) (Real.log 2),
      Φ ((Ω * C / D ^ 2) * Real.exp x) = ∫ τ : ℝ, g τ * sourceReflectedFourierPhase τ x) :
    Real.sqrt (∑ i, ‖∑ j, r i * K i j * (if keep j then a j else 0) *
      Φ (Ω * qC j / (qR i) ^ 2)‖ ^ 2) ≤
      (∫ τ : ℝ, ‖g τ‖) * U * Real.sqrt (∑ j, ‖if keep j then a j else 0‖ ^ 2) := by
  let u (i : Rows) := -2 * Real.log (qR i / D)
  let v (j : Cols) := Real.log (qC j / C)
  have hprofile (i : Rows) (j : Cols) : Φ (Ω * qC j / (qR i) ^ 2) =
      ∫ τ : ℝ, g τ * sourceReflectedFourierPhase τ (u i + v j) := by
    have he := hInv (u i + v j) (sourceReflectedDyad_logRatio_mem hD hC (hR i) (hQ j))
    have ha : (Ω * C / D ^ 2) * Real.exp (u i + v j) = Ω * qC j / (qR i) ^ 2 :=
      sourceReflectedDyad_profileArgument Ω hD hC (hD.trans_le (hR i).1) (hC.trans_le (hQ j).1)
    rwa [ha] at he
  simp_rw [hprofile]
  exact source_fourier_separated_column_energy K hU hK r hr
    (fun j => if keep j then a j else 0) u v g hg

end
end ArtinMatthews.SourceReflection
