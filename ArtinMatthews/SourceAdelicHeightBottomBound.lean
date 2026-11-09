module

public import ArtinMatthews.SourceKPAdelicTranslatedHeight


set_option backward.privateInPublic true
@[expose] public section

/-! The actual source height has a positive rational-translate lower bound
on every determinant-one adelic matrix. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory Matrix Matrix.GeneralLinearGroup
open OAI.RepresentationTheory.Weil.AdelicSplitting SourceArchJacquet
open scoped NumberField AdeleRing MatrixGroups Classical BigOperators
noncomputable section

theorem sourceSL2_exists_bottom_row {F : Type} [Field F] (q : F × F) (hq : q ≠ 0) :
    ∃ γ : SL(2, F), γ 1 0 = q.1 ∧ γ 1 1 = q.2 := by
  by_cases ha : q.1 = 0
  · have hb : q.2 ≠ 0 := by
      intro hb
      exact hq (Prod.ext ha hb)
    refine ⟨⟨!![q.2⁻¹, 0; q.1, q.2], ?_⟩, rfl, rfl⟩
    simp [Matrix.det_fin_two, hb]
  · refine ⟨⟨!![0, -q.1⁻¹; q.1, q.2], ?_⟩, rfl, rfl⟩
    simp [Matrix.det_fin_two, ha]

variable (F : Type) [Field F] [NumberField F] {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceSL2Adelic_height_lower_of_bottom_bound (h : SL(2, 𝔸[F])) {R : ℝ}
    (hR : 0 < R)
    (hfin₀ : (h 1 0).2 ∈ IntegralAdeles.Construction.finiteIntegralRing F)
    (hfin₁ : (h 1 1).2 ∈ IntegralAdeles.Construction.finiteIntegralRing F)
    (harch : ∀ v : InfinitePlace F, ‖(h 1 0).1 v‖ ≤ R ∧ ‖(h 1 1).1 v‖ ≤ R) :
    (∏ v : InfinitePlace F, (1 / (2 * R ^ 2)) ^ v.mult) ≤
      sourceKPAdelicHeight F hζ h.toGL := by
  have hdet : GeneralLinearGroup.det h.toGL = 1 := Matrix.SpecialLinearGroup.coeToGL_det h
  have hI (v : InfinitePlace F) :
      1 / (2 * R ^ 2) ≤ sourceArchHeight (sourceKPAdelicBaseComplexAt F hζ v h.toGL) := by
    have hd : (GeneralLinearGroup.det (sourceKPAdelicBaseComplexAt F hζ v h.toGL) : ℂ) = 1 := by
      rw [← sourceKPAdelicComplexCoordinate_det, hdet]
      simp [sourceKPIdeleInfiniteCoordinate]
    have h₀ : ‖sourceKPAdelicBaseComplexAt F hζ v h.toGL 1 0‖ ≤ R := by
      change ‖sourceKPArchComplexEquiv F hζ v ((h 1 0).1 v)‖ ≤ R
      rw [sourceKPArchComplexEquiv_norm]
      exact (harch v).1
    have h₁ : ‖sourceKPAdelicBaseComplexAt F hζ v h.toGL 1 1‖ ≤ R := by
      change ‖sourceKPArchComplexEquiv F hζ v ((h 1 1).1 v)‖ ≤ R
      rw [sourceKPArchComplexEquiv_norm]
      exact (harch v).2
    have hb : sourceArchBottomNorm (sourceKPAdelicBaseComplexAt F hζ v h.toGL) ≤ 2 * R ^ 2 := by
      unfold sourceArchBottomNorm
      nlinarith [norm_nonneg (sourceKPAdelicBaseComplexAt F hζ v h.toGL 1 0),
        norm_nonneg (sourceKPAdelicBaseComplexAt F hζ v h.toGL 1 1)]
    unfold sourceArchHeight
    rw [hd, norm_one]
    exact one_div_le_one_div_of_le (sourceArchBottomNorm_pos _) hb
  have hF (P : HeightOneSpectrum (𝓞 F)) :
      1 ≤ sourceKPFiniteMatrixHeight F P (sourceKPAdelicBaseFiniteAt F P h.toGL) := by
    have hd : (GeneralLinearGroup.det (sourceKPAdelicBaseFiniteAt F P h.toGL) : P.adicCompletion F) = 1 := by
      rw [← sourceKPAdelicFiniteCoordinate_det, hdet]
      simp [sourceKPIdeleFiniteCoordinate]
    have h₀ : ‖sourceKPAdelicBaseFiniteAt F P h.toGL 1 0‖ ≤ 1 := by
      change ‖(h 1 0).2 P‖ ≤ 1
      exact Valued.toNormedField.norm_le_one_iff.mpr (hfin₀ P)
    have h₁ : ‖sourceKPAdelicBaseFiniteAt F P h.toGL 1 1‖ ≤ 1 := by
      change ‖(h 1 1).2 P‖ ≤ 1
      exact Valued.toNormedField.norm_le_one_iff.mpr (hfin₁ P)
    have hm : sourceKPBottomMax (sourceKPAdelicBaseFiniteAt F P h.toGL) ≤ 1 := max_le h₀ h₁
    have hp := sourceKPBottomMax_pos (sourceKPAdelicBaseFiniteAt F P h.toGL)
    unfold sourceKPFiniteMatrixHeight
    rw [hd, norm_one]
    apply (le_div_iff₀ (sq_pos_of_pos hp)).mpr
    nlinarith
  have harchProd : (∏ v : InfinitePlace F, (1 / (2 * R ^ 2)) ^ v.mult) ≤
      ∏ v : InfinitePlace F, sourceArchHeight (sourceKPAdelicBaseComplexAt F hζ v h.toGL) ^ v.mult := by
    apply Finset.prod_le_prod₀
    · intro v _
      positivity
    · intro v _
      exact pow_le_pow_left₀ (by positivity) (hI v) v.mult
  have hfiniteProd : 1 ≤ ∏ᶠ P : HeightOneSpectrum (𝓞 F),
      sourceKPFiniteMatrixHeight F P (sourceKPAdelicBaseFiniteAt F P h.toGL) := by
    rw [finprod_eq_prod _ (sourceKPAdelicFiniteHeight_finite_support F h.toGL)]
    exact Finset.one_le_prod₀ (fun P _ => hF P)
  calc
    _ = (∏ v : InfinitePlace F, (1 / (2 * R ^ 2)) ^ v.mult) * 1 := (mul_one _).symm
    _ ≤ (∏ v : InfinitePlace F, sourceArchHeight (sourceKPAdelicBaseComplexAt F hζ v h.toGL) ^ v.mult) *
        ∏ᶠ P : HeightOneSpectrum (𝓞 F), sourceKPFiniteMatrixHeight F P
          (sourceKPAdelicBaseFiniteAt F P h.toGL) :=
      mul_le_mul harchProd hfiniteProd zero_le_one
        (Finset.prod_nonneg (fun v _ => pow_nonneg (sourceArchHeight_pos _).le _))
    _ = _ := by
      simpa only [sourceKPFiniteMatrixHeight, sourceKPBottomMax] using
        (sourceKPAdelicHeight_product F hζ h.toGL).symm

end
end ArtinMatthews
