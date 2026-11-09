module

public import ArtinMatthews.SourceSLocalSheetMellin
public import Mathlib.MeasureTheory.Measure.Haar.Unique


set_option backward.privateInPublic true
@[expose] public section

/-! Inversion and translation on the actual norm-one group transport a
reflected integrand between the two literal norm sheets. -/
namespace ArtinMatthews.SourcePhysical
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped NumberField Classical
noncomputable section

variable {K : Type} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (ν : Measure (SNormOne K S)) [ν.IsHaarMeasure]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

private theorem sheetReflection_change (a : SWholeUnits K S) {T : ℝ} (hT : 0 < T) :
    ∃ e : SNormOne K S ≃ᵐ SNormOne K S, MeasurePreserving e ν ν ∧
      ∀ n : SNormOne K S,
        a * ((n : SWholeUnits K S) * sLocalPositiveScaling K hζ S T)⁻¹ =
          (e n : SWholeUnits K S) * sLocalPositiveScaling K hζ S (sLocalNorm K S a / T) := by
  let : LocallyCompactSpace (SNormOne K S) := sNormOne_locallyCompact K S
  let : PolishSpace (SNormOne K S) := sNormOne_polish K S
  let u := a * (sLocalPositiveScaling K hζ S T)⁻¹
  let v := sLocalPositiveScaling K hζ S (sLocalNorm K S a / T)
  have hn : sLocalNorm K S u = sLocalNorm K S v := by
    dsimp only [u, v]
    rw [sLocalNorm_mul, sLocalNorm_inv, sLocalPositiveScaling_norm K hζ S hT,
      sLocalPositiveScaling_norm K hζ S (div_pos (sLocalNorm_pos K S a) hT),
      div_eq_mul_inv]
  let k := sourceSLocalSameNormRatio S u v hn
  have hk : (k : SWholeUnits K S) * v = u := sourceSLocalSameNormRatio_mul S u v hn
  let e := (MeasurableEquiv.inv (SNormOne K S)).trans (MeasurableEquiv.mulLeft k)
  refine ⟨e, ?_, ?_⟩
  · exact (measurePreserving_mul_left ν k).comp (Measure.measurePreserving_inv ν)
  · intro n
    change a * ((n : SWholeUnits K S) * sLocalPositiveScaling K hζ S T)⁻¹ =
      ((k : SWholeUnits K S) * (n : SWholeUnits K S)⁻¹) * v
    rw [mul_inv_rev, mul_comm (k : SWholeUnits K S) (n : SWholeUnits K S)⁻¹, mul_assoc, hk]
    dsimp only [u]
    ac_rfl

theorem sourceSLocalSheetProfile_reflection (F : SWholeUnits K S → ℂ)
    (a : SWholeUnits K S) {T : ℝ} (hT : 0 < T) :
    sourceSLocalSheetProfile S ν hζ (fun x => F (a * x⁻¹)) T =
      sourceSLocalSheetProfile S ν hζ F (sLocalNorm K S a / T) := by
  obtain ⟨e,he,heq⟩ := sheetReflection_change S ν hζ a hT
  unfold sourceSLocalSheetProfile
  calc
    _ = ∫ n : SNormOne K S, F ((e n : SWholeUnits K S) *
          sLocalPositiveScaling K hζ S (sLocalNorm K S a / T)) ∂ν :=
      integral_congr_ae (Filter.Eventually.of_forall fun n => congrArg F (heq n))
    _ = _ := he.integral_comp' (fun n : SNormOne K S => F ((n : SWholeUnits K S) *
      sLocalPositiveScaling K hζ S (sLocalNorm K S a / T)))

theorem sourceSLocalSheetProfile_reflection_integrable_iff (F : SWholeUnits K S → ℂ)
    (a : SWholeUnits K S) {T : ℝ} (hT : 0 < T) :
    Integrable (fun n : SNormOne K S =>
      F (a * ((n : SWholeUnits K S) * sLocalPositiveScaling K hζ S T)⁻¹)) ν ↔
    Integrable (fun n : SNormOne K S =>
      F ((n : SWholeUnits K S) * sLocalPositiveScaling K hζ S (sLocalNorm K S a / T))) ν := by
  obtain ⟨e,he,heq⟩ := sheetReflection_change S ν hζ a hT
  let G (n : SNormOne K S) :=
    F ((n : SWholeUnits K S) * sLocalPositiveScaling K hζ S (sLocalNorm K S a / T))
  have hfun : (fun n : SNormOne K S =>
      F (a * ((n : SWholeUnits K S) * sLocalPositiveScaling K hζ S T)⁻¹)) = G ∘ e :=
    funext fun n => congrArg F (heq n)
  rw [hfun]
  exact he.integrable_comp_emb e.measurableEmbedding

end
end ArtinMatthews.SourcePhysical
