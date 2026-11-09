module

public import ArtinMatthews.PrincipalDedekindProbeGrowth
public import ArtinMatthews.SourcePrincipalSimplePoleShift


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Complex Set VaryingKummerAnalytic SourcePhysical
open OAI.SevenEighths.ProbePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K]

/-- Positive-line one-pole shift for the principal norm transform. The
lower line stays inside the holomorphic Mellin region of the weight. -/
theorem quadraticHeckePositivePrincipalShift (H : ℂ → ℂ) {σ X : ℝ}
    (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hX : 0 < X)
    (hH : DifferentiableOn ℂ H {z : ℂ | σ ≤ z.re ∧ z.re ≤ 5 / 4})
    (hrapid : ∀ m : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ s : ℂ, σ ≤ s.re → s.re ≤ 5 / 4 →
      (1 + |s.im|) ^ m * ‖H s‖ ≤ B) :
    let f := fun s : ℂ => (X : ℂ) ^ s * H s * mixedDedekindZeta K s
    verticalIntegral (5 / 4) f =
      verticalIntegral σ f + (dedekindZeta_residue K : ℂ) * (X : ℂ) * H 1 := by
  let f := fun s : ℂ => (X : ℂ) ^ s * H s * mixedDedekindZeta K s
  let A := fun s : ℂ => (X : ℂ) ^ s * H s * principalDedekindRegularized K s
  let δ := min (1 - σ) (1 / 4)
  have hδ : 0 < δ := lt_min (sub_pos.mpr hσ₁) (by norm_num)
  obtain ⟨C, m, hC, hζ⟩ := exists_mixedDedekindZeta_strip_bound_away_pole K
  obtain ⟨B, _, hB⟩ := hrapid (m + 2)
  let D := max (X ^ σ) (X ^ (5 / 4 : ℝ))
  have hD : 0 ≤ D := (Real.rpow_nonneg hX.le _).trans (le_max_left _ _)
  let E := D * (C / δ) * (2 ^ m * B)
  have hbound (s : ℂ) (hs : σ ≤ s.re) (hs' : s.re ≤ 5 / 4) (hd : δ ≤ ‖s - 1‖) :
      ‖f s‖ ≤ E * sourceContourHeightWeight s.im := by
    have hXs : ‖(X : ℂ) ^ s‖ ≤ D := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
      rcases le_total X 1 with hx | hx
      · exact (Real.rpow_le_rpow_of_exponent_ge hX hx hs).trans (le_max_left _ _)
      · exact (Real.rpow_le_rpow_of_exponent_le hx hs').trans (le_max_right _ _)
    have hZ := hζ δ hδ s (by linarith) hs' hd
    have hM := sourceContourHeightWeight_of_rapid m s.im B _ (norm_nonneg _) (hB s hs hs')
    unfold f
    rw [norm_mul, norm_mul]
    calc
      _ ≤ D * ‖H s‖ * (C / δ * (|s.im| + 2) ^ m) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_right hXs (norm_nonneg _)) hZ (norm_nonneg _)
          (mul_nonneg hD (norm_nonneg _))
      _ = (D * (C / δ)) * ((|s.im| + 2) ^ m * ‖H s‖) := by ring
      _ ≤ (D * (C / δ)) * ((2 ^ m * B) * sourceContourHeightWeight s.im) :=
        mul_le_mul_of_nonneg_left hM (mul_nonneg hD (div_nonneg hC.le hδ.le))
      _ = _ := by unfold E; ring
  have hA : DifferentiableOn ℂ A {z : ℂ | σ ≤ z.re ∧ z.re ≤ 5 / 4} :=
    (((differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))).differentiableOn).mul hH).mul
      (principalDedekindRegularized_entire K).differentiableOn
  have hratio (s : ℂ) (hs : s ≠ 1) : f s = A s / (s - 1) := by
    unfold f A
    rw [principalDedekindRegularized_eq_zeta K hs]
    field_simp [sub_ne_zero.mpr hs]
  have hline (a t : ℝ) (ha : σ ≤ a) (ha' : a ≤ 5 / 4)
      (hd : δ ≤ |a - 1| ∨ 1 ≤ |t|) :
      ‖f ((a : ℂ) + t * I)‖ ≤ E * sourceContourHeightWeight t := by
    have hd' : δ ≤ ‖((a : ℂ) + (t : ℂ) * I) - 1‖ := by
      rcases hd with hd | ht
      · exact hd.trans (by simpa using Complex.abs_re_le_norm (((a : ℂ) + (t : ℂ) * I) - 1))
      · exact (min_le_right (1 - σ) (1 / 4)).trans
          ((show (1 / 4 : ℝ) ≤ 1 by norm_num).trans (ht.trans
            (by simpa using Complex.abs_im_le_norm (((a : ℂ) + (t : ℂ) * I) - 1))))
    simpa using hbound ((a : ℂ) + (t : ℂ) * I) (by simpa using ha) (by simpa using ha') hd'
  have hσb : σ ≤ (5 / 4 : ℝ) := by linarith
  have hdLeft : δ ≤ |σ - 1| := by
    rw [abs_of_nonpos (sub_nonpos.mpr hσ₁.le), neg_sub]
    exact min_le_left _ _
  have hdRight : δ ≤ |5 / 4 - 1| := by
    convert min_le_right (1 - σ) (1 / 4) using 1
    norm_num
  have he := source_verticalIntegral_simple_pole_of_heightWeight A f
    (a := σ) (b := 5 / 4) (p := 1) (C := E) hσ₁ (by norm_num) hA
    (fun z _ _ hz => hratio z (by simpa using hz))
    (fun t => hline σ t le_rfl hσb (Or.inl hdLeft))
    (fun t => hline (5 / 4) t hσb le_rfl (Or.inl hdRight))
    (fun a ha t ht => hline a t ha.1 ha.2 (Or.inr ht))
  simpa [A, f, principalDedekindRegularized_one, mul_comm, mul_left_comm, mul_assoc] using he

end
end ArtinMatthews
