module

public import ArtinMatthews.SourceSLocalExactMeasures
public import ArtinMatthews.SourceSLocalTensorSheet
public import ArtinMatthews.SourceComplexUnitMellinValue


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory Filter
open ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField Classical SchwartzMap
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (v : InfinitePlace K)
include hζ in
theorem sourceSLocalComplexPlace : IsComplex v := (source_isTotallyComplex K hζ).isComplex v

local notation "hv" => (sourceSLocalComplexPlace K hζ v)

def sourceSLocalWholeMellinIntegrand (g : 𝓢(ℂ, ℂ)) (G : SNormOneOtherUnits S v → ℂ)
    (s : ℂ) (x : SWholeUnits K S) : ℂ :=
  sourceSLocalChosenTensor S hv g G x * (sLocalNorm K S x : ℂ) ^ s

theorem sourceSLocalWholeMellinIntegrand_split (g : 𝓢(ℂ, ℂ))
    (G : SNormOneOtherUnits S v → ℂ) (s : ℂ) (x : SWholeUnits K S) :
    sourceSLocalWholeMellinIntegrand K hζ S v g G s x =
      sourceComplexUnitMellinIntegrand g s (sourceComplexPlaceUnitsEquiv hv (x.1 v)) *
      (G (sourceSheetOther S v x) *
        (sourceSheetOtherNorm S v (sourceSheetOther S v x) : ℂ) ^ s) := by
  rw [sourceSLocalWholeMellinIntegrand, sourceSLocalChosenTensor, sourceSheetWholeNorm_split S v,
    (show v.mult = 2 from (sourceSLocalComplexPlace K hζ v).mult_eq_two), Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (sq_nonneg _)
      (sourceSheetOtherNorm_pos S v _).le, sourceComplexUnitMellinIntegrand,
    sourceComplexPlaceUnitsEquiv_val, sourceSheetComplex_norm]
  ac_rfl

theorem sourceSLocalWholeMellinIntegrand_integrable (g : 𝓢(ℂ, ℂ))
    (G : SNormOneOtherUnits S v → ℂ) (s : ℂ) (hs : 0 < s.re)
    (hG : Integrable (fun y => G y * (sourceSheetOtherNorm S v y : ℂ) ^ s)
      (sourceSLocalOtherUnitMeasure K hζ S v)) :
    Integrable (sourceSLocalWholeMellinIntegrand K hζ S v g G s)
      (sourceSLocalUnitProductMeasure K hζ S) := by
  let A : v.Completionˣ → ℂ := fun z =>
    sourceComplexUnitMellinIntegrand g s (sourceComplexPlaceUnitsEquiv hv z)
  let B : SNormOneOtherUnits S v → ℂ := fun y => G y * (sourceSheetOtherNorm S v y : ℂ) ^ s
  have hA : Integrable A (sourceSLocalArchUnitMeasure K hζ v) :=
    sourceComplexPlaceUnitMellinIntegrand_integrable hv g s hs
  have : SigmaFinite (sourceSLocalOtherUnitMeasure K hζ S v) := by
    unfold sourceSLocalOtherUnitMeasure sourceSheetOtherMeasure
    infer_instance
  have hmp : MeasurePreserving (sourceSWholeSheetSplit S v) (sourceSLocalUnitProductMeasure K hζ S)
      ((sourceSLocalArchUnitMeasure K hζ v).prod (sourceSLocalOtherUnitMeasure K hζ S v)) :=
    sourceSWholeSheetSplit_measurePreserving S v (sourceSLocalArchUnitMeasure K hζ)
      (sourceSLocalFiniteUnitMeasure K S)
  have hi := hmp.integrable_comp_of_integrable (hA.mul_prod hG)
  apply hi.congr
  filter_upwards with x
  exact (sourceSLocalWholeMellinIntegrand_split K hζ S v g G s x).symm

theorem sourceSLocalWholeMellin_eq_product (g : 𝓢(ℂ, ℂ))
    (G : SNormOneOtherUnits S v → ℂ) (s : ℂ) :
    (∫ x, sourceSLocalWholeMellinIntegrand K hζ S v g G s x
      ∂sourceSLocalUnitProductMeasure K hζ S) =
      sourceComplexMellin g s * ∫ y, G y * (sourceSheetOtherNorm S v y : ℂ) ^ s
        ∂sourceSLocalOtherUnitMeasure K hζ S v := by
  let A : v.Completionˣ → ℂ := fun z =>
    sourceComplexUnitMellinIntegrand g s (sourceComplexPlaceUnitsEquiv hv z)
  let B : SNormOneOtherUnits S v → ℂ := fun y => G y * (sourceSheetOtherNorm S v y : ℂ) ^ s
  have : SigmaFinite (sourceSLocalOtherUnitMeasure K hζ S v) := by
    unfold sourceSLocalOtherUnitMeasure sourceSheetOtherMeasure
    infer_instance
  have hmp : MeasurePreserving (sourceSWholeSheetSplit S v) (sourceSLocalUnitProductMeasure K hζ S)
      ((sourceSLocalArchUnitMeasure K hζ v).prod (sourceSLocalOtherUnitMeasure K hζ S v)) :=
    sourceSWholeSheetSplit_measurePreserving S v (sourceSLocalArchUnitMeasure K hζ)
      (sourceSLocalFiniteUnitMeasure K S)
  let e := sourceSWholeSheetSplitMeasurableEquiv S v
  have he : MeasurePreserving e (sourceSLocalUnitProductMeasure K hζ S)
      ((sourceSLocalArchUnitMeasure K hζ v).prod (sourceSLocalOtherUnitMeasure K hζ S v)) := hmp
  calc
    _ = ∫ x, A (e x).1 * B (e x).2 ∂sourceSLocalUnitProductMeasure K hζ S :=
      integral_congr_ae (Eventually.of_forall (sourceSLocalWholeMellinIntegrand_split K hζ S v g G s))
    _ = ∫ p, A p.1 * B p.2
        ∂(sourceSLocalArchUnitMeasure K hζ v).prod (sourceSLocalOtherUnitMeasure K hζ S v) :=
      he.integral_comp' (fun p => A p.1 * B p.2)
    _ = _ := by
      rw [integral_prod_mul A B]
      have hA : (∫ z, A z ∂sourceSLocalArchUnitMeasure K hζ v) = sourceComplexMellin g s :=
        sourceComplexPlaceUnitHaar_mellin_eq hv g s
      rw [hA]

end
end ArtinMatthews.SourcePhysical
