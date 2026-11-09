module

public import ArtinMatthews.SourceComplexIdealBasis


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory Module NumberField NumberField.InfinitePlace Set
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section

theorem sourceComplexProductMeasure_eq_smul_volume (ι : Type*) [Fintype ι] :
    sourceComplexProductMeasure ι =
      ((2 : ENNReal) ^ Fintype.card ι) • (volume : Measure (ι → ℂ)) := by
  unfold sourceComplexProductMeasure
  apply Measure.pi_eq
  intro s _
  rw [Measure.smul_apply, volume_pi, Measure.pi_pi]
  simp only [sourceComplexTraceMeasure, Measure.smul_apply, smul_eq_mul,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

theorem sourceComplexBasisHaarFactor_eq_fundamentalDomain
    {ι κ : Type*} [Fintype ι] [Fintype κ] (b : Basis κ ℝ (ι → ℂ)) :
    (OAI.RepresentationTheory.Weil.AdelicSplitting.LatticePoisson.LocalAnalysis.basisHaarFactor
      b (sourceComplexProductMeasure ι) : ℝ) =
      (sourceComplexProductMeasure ι).real (ZSpan.fundamentalDomain b) := by
  let μ := sourceComplexProductMeasure ι
  let c := OAI.RepresentationTheory.Weil.AdelicSplitting.LatticePoisson.LocalAnalysis.basisHaarFactor b μ
  let cube : Set (κ → ℝ) := Set.pi univ (fun _ => Ico 0 1)
  have hc : MeasurableSet cube := MeasurableSet.pi countable_univ (fun _ _ => measurableSet_Ico)
  have hv : volume cube = 1 := by
    rw [show cube = _ from rfl, volume_pi, Measure.pi_pi]
    simp [Real.volume_Ico]
  have he : b.equivFunL ⁻¹' cube = ZSpan.fundamentalDomain b := by
    ext x
    simp [cube, ZSpan.mem_fundamentalDomain, Set.mem_pi, Basis.equivFunL_apply]
  have : (μ.map b.equivFunL).IsAddHaarMeasure := b.equivFunL.isAddHaarMeasure_map μ
  have hmap : μ.map b.equivFunL = c • volume := Measure.isAddLeftInvariant_eq_smul_of_regular _ _
  have h := congrArg (fun ν : Measure (κ → ℝ) => ν cube) hmap
  rw [Measure.map_apply b.equivFunL.continuous.measurable hc, he,
    Measure.smul_apply, hv] at h
  change μ (ZSpan.fundamentalDomain b) = (c : ENNReal) * 1 at h
  rw [mul_one] at h
  exact congrArg ENNReal.toReal h.symm

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]

theorem sourceMixedComplexEquiv_volumePreserving : MeasurePreserving (sourceMixedComplexEquiv K) := by
  refine ⟨(sourceMixedComplexEquiv K).continuous.measurable, ?_⟩
  have := source_complex_real_places_empty K
  change Measure.map Prod.snd ((volume : Measure ({v : InfinitePlace K // IsReal v} → ℝ)).prod
    (volume : Measure ({v : InfinitePlace K // IsComplex v} → ℂ))) = volume
  rw [Measure.map_snd_prod]
  have h : (volume : Measure ({v : InfinitePlace K // IsReal v} → ℝ)) univ = 1 := by
    rw [volume_pi]
    exact Measure.pi_empty_univ (fun _ : {v : InfinitePlace K // IsReal v} => (volume : Measure ℝ))
  rw [h, one_smul]

theorem sourceEuclideanComplexEquiv_volumePreserving :
    MeasurePreserving (sourceEuclideanComplexEquiv K) :=
  (sourceMixedComplexEquiv_volumePreserving K).comp
    (mixedEmbedding.euclidean.volumePreserving_toMixed K)

variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

theorem sourceIdealComplexBasis_fundamentalDomain_volume :
    volume.real (ZSpan.fundamentalDomain (sourceIdealComplexBasis K I)) =
      ZLattice.covolume (mixedIdealLattice K I) := by
  let b := mixedIdealEuclideanBasis K I
  let e := sourceEuclideanComplexEquiv K
  have himage : e '' ZSpan.fundamentalDomain b =
      ZSpan.fundamentalDomain (sourceIdealComplexBasis K I) :=
    ZSpan.map_fundamentalDomain b e.toLinearEquiv
  have hpre : e ⁻¹' ZSpan.fundamentalDomain (sourceIdealComplexBasis K I) =
      ZSpan.fundamentalDomain b := by
    rw [← himage, Set.preimage_image_eq _ e.injective]
  have hmeas : MeasurableSet (ZSpan.fundamentalDomain (sourceIdealComplexBasis K I)) :=
    ZSpan.fundamentalDomain_measurableSet _
  have hm := sourceEuclideanComplexEquiv_volumePreserving K
  rw [← hm.map_eq, measureReal_def, Measure.map_apply hm.measurable hmeas, hpre,
    ← measureReal_def]
  have hb : (mixedIdealIntegralBasis K I).ofZLatticeBasis ℝ = b := by
    ext i
    simp only [Basis.ofZLatticeBasis_apply, mixedIdealIntegralBasis_apply, b]
  have h := ZLattice.covolume_eq_measure_fundamentalDomain (mixedIdealLattice K I)
    volume (ZLattice.isAddFundamentalDomain (mixedIdealIntegralBasis K I) volume)
  rw [hb] at h
  exact h.symm

/-- Twice planar measure at each complex place cancels the factor 2^-r₂
in the Euclidean ideal covolume. The exact source Poisson multiplier remains. -/
theorem sourceIdealComplexBasis_haar_factor :
    (OAI.RepresentationTheory.Weil.AdelicSplitting.LatticePoisson.LocalAnalysis.basisHaarFactor
      (sourceIdealComplexBasis K I) (sourceComplexProductMeasure {v : InfinitePlace K // IsComplex v}) : ℝ) =
        (FractionalIdeal.absNorm I.1 : ℝ) * Real.sqrt |(discr K : ℝ)| := by
  rw [sourceComplexBasisHaarFactor_eq_fundamentalDomain,
    sourceComplexProductMeasure_eq_smul_volume, measureReal_ennreal_smul_apply,
    sourceIdealComplexBasis_fundamentalDomain_volume, mixedIdealLattice_covolume]
  simp only [ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  change (2 : ℝ) ^ nrComplexPlaces K * _ = _
  rw [inv_pow]
  field_simp

end
end ArtinMatthews.VaryingKummerAnalytic
