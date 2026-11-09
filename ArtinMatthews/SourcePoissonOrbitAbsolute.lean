module

public import ArtinMatthews.SourcePoissonOrbitRows
public import ArtinMatthews.SourcePoissonDominatedSeries


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open MeasureTheory
noncomputable section

theorem sourcePoisson_summable_norm_scaled_integral
    {α ι : Type} [MeasurableSpace α] {μ : Measure α}
    (f : ι → α → ℂ) (hf : Summable (fun i => ∫ p, ‖f i p‖ ∂μ)) (C : ℂ) :
    Summable (fun i => ‖C * ∫ p, f i p ∂μ‖) := by
  simp_rw [norm_mul]
  have h0 (i : ι) : 0 ≤ ‖C‖ * ‖∫ p, f i p ∂μ‖ :=
    mul_nonneg (norm_nonneg C) (norm_nonneg (∫ p, f i p ∂μ))
  have hLe (i : ι) : ‖C‖ * ‖∫ p, f i p ∂μ‖ ≤ ‖C‖ * ∫ p, ‖f i p‖ ∂μ :=
    mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm (f i)) (norm_nonneg C)
  exact Summable.of_nonneg_of_le h0 hLe (hf.mul_left ‖C‖)

end
end ArtinMatthews.SourcePhysical

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain MeasureTheory AllowedGenerators
open VaryingKummerAnalytic QuadraticWeil SourcePhysical
open scoped NumberField Classical ContDiff BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)
variable (v : InfinitePlace F)

theorem sourcePoissonOrbitRow_summable_norm
    (W₁ : ℝ → ℂ) (hcompact : HasCompactSupport W₁)
    (hpositive : tsupport W₁ ⊆ Set.Ioi 0) (hsmooth : ContDiff ℝ ∞ W₁)
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (u : {u : sourceRing F S₀ // u ≠ 0}) :
    Summable fun a : SourceExponentCoordinates F S₀ =>
      ‖sourcePoissonOrbitTerm F S₀ hζ hS η v W₁ X Y Z u a‖ := by
  let W (y : ℝ) := mellin W₁ (sourcePoissonVertical 4 y)
  let M (y : ℝ) := sourceSLocalProbeMellin F hζ (sourceHilbertSet F S₀) v (sourcePoissonVertical 2 y)
  let K := sourcePoissonFrequencyKernel F S₀ X Y Z W M u
  let A (a : SourceExponentCoordinates F S₀) (p : SourcePoissonHeights) :=
    sourceGlobalEulerTerm F hζ S₀ hS η u.val
      (sourcePoissonVertical 4 p.2) (sourcePoissonVertical 4 p.1.1) (sourcePoissonVertical 2 p.1.2) a
  let B := sourceCoordinateMajorant F S₀ 3 10 3 12
  have hK : Integrable K sourcePoissonHeightMeasure :=
    sourcePoissonFrequencyKernel_integrable F S₀ hX hY hZ W M
      (smoothMellin_verticalIntegrable W₁ hcompact hpositive hsmooth 4)
      (sourceSLocalProbeMellin_verticalIntegrable F hζ (sourceHilbertSet F S₀) v 2 (by norm_num))
      ((smoothMellin_entire W₁ hcompact hpositive hsmooth.continuous).continuous.comp
        (sourcePoissonVertical_continuous 4)).measurable
      (sourceSLocalProbeMellin_continuous_vertical F S₀ hζ v (by norm_num)).measurable u
  have hA (a : SourceExponentCoordinates F S₀) : Measurable (A a) :=
    (sourceGlobalEulerTerm_initial_continuous F S₀ hζ hS η u.val a).measurable
  have hB : Summable B :=
    sourceCoordinateMajorant_summable F S₀ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hbound (a : SourceExponentCoordinates F S₀) (p : SourcePoissonHeights) : ‖A a p‖ ≤ B a := by
    have h := sourceGlobalEulerTerm_norm_le F S₀ hζ hS η u.val
      (sourcePoissonVertical 4 p.2) (sourcePoissonVertical 4 p.1.1) (sourcePoissonVertical 2 p.1.2) a
    norm_num only [sourcePoissonVertical_re] at h
    exact h
  let : Countable (Ideal (𝓞 F)) := by
    apply Set.countable_univ_iff.mp
    apply (Set.countable_iUnion (fun n : ℕ =>
      (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) n).countable)).mono
    intro I _
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨Ideal.absNorm I, le_rfl⟩
  let : Countable (HeightOneSpectrum (𝓞 F)) := HeightOneSpectrum.asIdeal_injective.countable
  have hNorm := (sourcePoisson_mul_tsum_integrable_and_summable K hK A hA B hB hbound).2
  simp_rw [sourcePoissonOrbitTerm_eq_initialContour F S₀ hζ hS η v W₁ hcompact hpositive
    hsmooth hX hY hZ u]
  exact sourcePoisson_summable_norm_scaled_integral (fun a p => K p * A a p)
    hNorm (sourcePoissonNormalization ^ 3)

end
end ArtinMatthews.SourceEulerAssembly
