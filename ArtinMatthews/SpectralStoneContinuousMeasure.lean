module

public import ArtinMatthews.SpectralStoneMeasureOnRegular


set_option backward.privateInPublic true
@[expose] public section

/-! The regular scalar measure is absolutely continuous in the actual
energy variable, with its zero extension across exceptional points. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace ArtinMatthews

def gamma0StoneDensityExtension (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) : ℝ → ℝ :=
  (gamma0StoneGoodEnergy N ψ Y).indicator (gamma0StoneBoundaryDensity N ψ Y)

theorem gamma0StoneBoundaryDensity_measurable (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) :
    Measurable (gamma0StoneBoundaryDensity N ψ Y) := by
  let U := gamma0StoneGoodEnergy N ψ Y
  have hc : (Uᶜ : Set ℝ).Countable := gamma0StoneGoodEnergy_compl_countable N ψ Y
  let _ : Countable ↥(Uᶜ : Set ℝ) := hc.to_subtype
  apply measurable_of_restrict_of_restrict_compl (gamma0StoneGoodEnergy_open N ψ Y).measurableSet
  · exact (gamma0StoneBoundaryDensity_continuousOn N ψ Y).domRestrict.measurable
  · exact measurable_of_countable _

theorem gamma0StoneDensityExtension_measurable (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) :
    Measurable (gamma0StoneDensityExtension N ψ Y) :=
  (gamma0StoneBoundaryDensity_measurable N ψ Y).indicator (gamma0StoneGoodEnergy_open N ψ Y).measurableSet

theorem gamma0StoneDensityExtension_nonneg (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) (x : ℝ) :
    0 ≤ gamma0StoneDensityExtension N ψ Y x := by
  by_cases hx : x∈gamma0StoneGoodEnergy N ψ Y
  · rw [gamma0StoneDensityExtension,indicator_of_mem hx]
    exact gamma0StoneBoundaryDensity_nonneg N ψ Y x hx
  · rw [gamma0StoneDensityExtension,indicator_of_notMem hx]

theorem gamma0StoneDensityExtension_zero_below (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) (x : ℝ) (hx : x≤1/4) :
    gamma0StoneDensityExtension N ψ Y x=0 := by
  by_cases h : x∈gamma0StoneGoodEnergy N ψ Y
  · rw [gamma0StoneDensityExtension,indicator_of_mem h]
    exact gamma0StoneBoundaryDensity_subcritical N ψ Y x h (lt_of_le_of_ne hx h.1)
  · rw [gamma0StoneDensityExtension,indicator_of_notMem h]

theorem gamma0StoneContinuousMeasure_apply (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) (s : Set ℝ) (hs : MeasurableSet s) :
    gamma0StoneContinuousMeasure N ψ Y s=
      ∫⁻ x in s∩gamma0StoneGoodEnergy N ψ Y,ENNReal.ofReal (gamma0StoneBoundaryDensity N ψ Y x) := by
  let U := gamma0StoneGoodEnergy N ψ Y
  let g := gamma0StoneBoundaryDensity N ψ Y
  have hU := (gamma0StoneGoodEnergy_open N ψ Y).measurableSet
  let v := Measure.comap ((↑) : U → ℝ) volume
  let ν := v.withDensity (fun x : U => ENNReal.ofReal (g x))
  have hE := MeasurableEmbedding.subtype_coe hU
  change Measure.map ((↑) : U → ℝ) ν s=∫⁻ x in s∩U,ENNReal.ofReal (g x)
  rw [Measure.map_apply hE.measurable hs]
  change ν (((↑) : U → ℝ) ⁻¹' s)=_
  rw [show ν=v.withDensity (fun x : U => ENNReal.ofReal (g x)) from rfl,
    withDensity_apply _ (hE.measurable hs)]
  calc
    _ = ∫⁻ x in ((↑) : U → ℝ) '' (((↑) : U → ℝ) ⁻¹' s),ENNReal.ofReal (g x) :=
      setLIntegral_subtype hU _ (fun x => ENNReal.ofReal (g x))
    _ = _ := by rw [Set.image_preimage_eq_inter_range,Subtype.range_coe]

theorem gamma0StoneContinuousMeasure_eq_withDensity (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) :
    gamma0StoneContinuousMeasure N ψ Y=
      volume.withDensity (fun x => ENNReal.ofReal (gamma0StoneDensityExtension N ψ Y x)) := by
  ext s hs
  let U := gamma0StoneGoodEnergy N ψ Y
  let g := gamma0StoneBoundaryDensity N ψ Y
  have hU := (gamma0StoneGoodEnergy_open N ψ Y).measurableSet
  have he : (fun x => ENNReal.ofReal (gamma0StoneDensityExtension N ψ Y x))=
      U.indicator (fun x => ENNReal.ofReal (g x)) := by
    funext x
    by_cases hx : x∈U
    · simp only [gamma0StoneDensityExtension,U,indicator_of_mem hx,g]
    · simp only [gamma0StoneDensityExtension,U,indicator_of_notMem hx,ENNReal.ofReal_zero]
  rw [gamma0StoneContinuousMeasure_apply N ψ Y s hs,he,withDensity_apply _ hs,
    lintegral_indicator hU,Measure.restrict_restrict hU,inter_comm]

theorem gamma0StoneContinuousMeasure_absolutelyContinuous (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (Y : Gamma0CompactResolventCutoff N ψ) :
    gamma0StoneContinuousMeasure N ψ Y ≪ volume := by
  rw [gamma0StoneContinuousMeasure_eq_withDensity N ψ Y]
  exact withDensity_absolutelyContinuous _ _

end ArtinMatthews
