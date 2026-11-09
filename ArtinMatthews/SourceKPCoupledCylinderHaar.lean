module

public import ArtinMatthews.SourceAdelicFiniteSelfDual
public import ArtinMatthews.SourceKPCoupledWildLower


set_option backward.privateInPublic true
@[expose] public section

/-! The compact cylinder with prescribed deep ideals at a finite set of
places has the exact standard Haar mass, including the different factors. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory SourcePhysical StandardAdelic Function
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField AdeleRing Topology Classical ENNReal BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K]

local instance coupledCylinderFiniteMeasurable : MeasurableSpace 𝔸ᶠ[K] := borel 𝔸ᶠ[K]
local instance coupledCylinderFiniteBorel : BorelSpace 𝔸ᶠ[K] := ⟨rfl⟩
local instance coupledCylinderLocalMeasurable (P : HeightOneSpectrum (𝓞 K)) :
    MeasurableSpace (P.adicCompletion K) := borel _
local instance coupledCylinderLocalBorel (P : HeightOneSpectrum (𝓞 K)) :
    BorelSpace (P.adicCompletion K) := ⟨rfl⟩

local notation "Oᶠ" => IntegralAdeles.Construction.finiteIntegralRing K

def sourceKPCoupledDeepCylinder (T : Finset (HeightOneSpectrum (𝓞 K))) : Set 𝔸ᶠ[K] :=
  {x | x ∈ Oᶠ ∧ ∀ P ∈ T, x P ∈ sourceKPDeepIdealImage K P}

theorem sourceKPCoupledDeepCylinder_measurable (T : Finset (HeightOneSpectrum (𝓞 K))) :
    MeasurableSet (sourceKPCoupledDeepCylinder K T) := by
  have he : sourceKPCoupledDeepCylinder K T = (Oᶠ : Set 𝔸ᶠ[K]) ∩
      ⋂ P : T, (fun x : 𝔸ᶠ[K] => x P.val) ⁻¹' sourceKPDeepIdealImage K P.val := by
    ext x
    simp [sourceKPCoupledDeepCylinder]
  rw [he]
  refine (IntegralAdeles.Construction.isOpen_finiteIntegralRing K).measurableSet.inter ?_
  apply MeasurableSet.iInter
  intro P
  have hcont : Continuous (fun x : 𝔸ᶠ[K] => x P.val) := RestrictedProduct.continuous_eval _
  exact (sourceKPDeepIdealImage_isOpen K P.val).measurableSet.preimage hcont.measurable

theorem sourceKPCoupledDeepCylinder_local_mass (P : HeightOneSpectrum (𝓞 K)) :
    sourceKPIntegralPlaceHaar K P
      ((Subtype.val : P.adicCompletionIntegers K → P.adicCompletion K) ⁻¹' sourceKPDeepIdealImage K P) =
    (sourceLocalSelfDual K P (P.adicCompletionIntegers K))⁻¹ *
      sourceLocalSelfDual K P (sourceKPDeepIdealImage K P) := by
  let i : P.adicCompletionIntegers K → P.adicCompletion K := Subtype.val
  let J := sourceKPDeepIdealImage K P
  have hi : MeasurableEmbedding i :=
    (Valued.isOpen_valuationSubring (P.adicCompletion K)).isOpenEmbedding_subtypeVal.measurableEmbedding
  have hr : i '' (i ⁻¹' J) = J := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      have hO : x ∈ P.adicCompletionIntegers K := by
        change x ∈ (P.adicCompletionIntegers K : Set (P.adicCompletion K))
        rw [← sourceLocalBall_zero K P]
        exact sourceKPCoupledDeepIdeal_subset_integer_ball K P hx
      exact ⟨⟨x, hO⟩, hx, rfl⟩
  change sourceKPIntegralPlaceHaar K P (i ⁻¹' J) = _
  rw [← sourceKPNormalizedLocalSelfDual_eq K P, sourceKPNormalizedLocalSelfDual,
    Measure.smul_apply, hi.comap_apply, hr]
  rfl

theorem sourceKPCoupledDeepCylinder_mass_normalized (T : Finset (HeightOneSpectrum (𝓞 K))) :
    sourceKPFiniteStandardHaar K (sourceKPCoupledDeepCylinder K T) =
      (sourceKPDiscriminantRoot K)⁻¹ *
        ∏ P ∈ T, (sourceLocalSelfDual K P (P.adicCompletionIntegers K))⁻¹ *
          sourceLocalSelfDual K P (sourceKPDeepIdealImage K P) := by
  let i : Oᶠ → 𝔸ᶠ[K] := Subtype.val
  let e := IntegralAdeles.Construction.finiteIntegralProductHomeomorph K
  let C := sourceKPCoupledDeepCylinder K T
  let J := fun P : HeightOneSpectrum (𝓞 K) =>
    (Subtype.val : P.adicCompletionIntegers K → P.adicCompletion K) ⁻¹' sourceKPDeepIdealImage K P
  have hi : MeasurableEmbedding i :=
    (IntegralAdeles.Construction.isOpen_finiteIntegralRing K).isOpenEmbedding_subtypeVal.measurableEmbedding
  have hiC : i '' (i ⁻¹' C) = C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx, rfl⟩
  have heC : e ⁻¹' (i ⁻¹' C) = (T : Set (HeightOneSpectrum (𝓞 K))).pi J := by
    ext x
    change ((i (e x) ∈ Oᶠ) ∧ (∀ P ∈ T, (i (e x)) P ∈ sourceKPDeepIdealImage K P)) ↔ _
    rw [and_iff_right (e x).property]
    rfl
  change sourceKPFiniteStandardHaar K C = _
  rw [← hiC, ← hi.comap_apply, sourceKPFiniteStandardHaarRestriction_eq_product K]
  rw [Measure.smul_apply, sourceKPFiniteIntegralProductHaar]
  change (sourceKPDiscriminantRoot K)⁻¹ *
    (Measure.map e (sourceKPIntegralProductHaar K)) (i ⁻¹' C) = _
  rw [Measure.map_apply e.continuous.measurable (hi.measurable (sourceKPCoupledDeepCylinder_measurable K T)),
    heC, sourceKPIntegralProductHaar, Measure.infinitePi_pi]
  · simp_rw [J, sourceKPCoupledDeepCylinder_local_mass K]
  · intro P _
    exact (sourceKPDeepIdealImage_isOpen K P).measurableSet.preimage continuous_subtype_val.measurable

theorem sourceKPCoupledSelfDual_integer_good (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ traceBadPlaces K) :
    sourceLocalSelfDual K P (P.adicCompletionIntegers K) = 1 := by
  have h := congrArg ENNReal.ofReal (sourceLocalSelfDual_volume_integer_of_good K P hP)
  rw [sourceLocalBall_zero K P] at h
  simpa only [Measure.real, ENNReal.ofReal_toReal (sourceKPLocalSelfDual_integer_ne_top K P),
    ENNReal.ofReal_one] using h

theorem sourceKPCoupledDeepCylinder_mass (T : Finset (HeightOneSpectrum (𝓞 K))) :
    sourceKPFiniteStandardHaar K (sourceKPCoupledDeepCylinder K T) =
      (∏ P ∈ traceBadPlaces K \ T, sourceLocalSelfDual K P (P.adicCompletionIntegers K)) *
        ∏ P ∈ T, sourceLocalSelfDual K P (sourceKPDeepIdealImage K P) := by
  let m := fun P : HeightOneSpectrum (𝓞 K) => sourceLocalSelfDual K P (P.adicCompletionIntegers K)
  let j := fun P : HeightOneSpectrum (𝓞 K) => sourceLocalSelfDual K P (sourceKPDeepIdealImage K P)
  let U := traceBadPlaces K ∪ T
  have hs : mulSupport m ⊆ U := by
    intro P hP
    by_contra h
    exact hP (sourceKPCoupledSelfDual_integer_good K P
      (fun hbad => h (Finset.mem_union_left _ hbad)))
  have hT : T ⊆ U := Finset.subset_union_right
  have hU : U \ T = traceBadPlaces K \ T := by
    ext P
    simp only [U, Finset.mem_sdiff, Finset.mem_union]
    tauto
  rw [sourceKPCoupledDeepCylinder_mass_normalized K T, ← sourceKPLocalSelfDual_integer_product K]
  change (∏ᶠ P, m P) * (∏ P ∈ T, (m P)⁻¹ * j P) = _
  rw [finprod_eq_prod_of_mulSupport_subset m hs, ← Finset.prod_sdiff hT, hU,
    mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro P _
  rw [← mul_assoc, ENNReal.mul_inv_cancel (sourceKPLocalSelfDual_integer_ne_zero K P)
    (sourceKPLocalSelfDual_integer_ne_top K P), one_mul]

theorem sourceKPCoupledDeepCylinder_real_mass (T : Finset (HeightOneSpectrum (𝓞 K))) :
    (sourceKPFiniteStandardHaar K).real (sourceKPCoupledDeepCylinder K T) =
      (∏ P ∈ traceBadPlaces K \ T, (sourceLocalSelfDual K P).real (P.adicCompletionIntegers K)) *
        ∏ P ∈ T, (sourceLocalSelfDual K P).real (sourceKPDeepIdealImage K P) := by
  rw [Measure.real, sourceKPCoupledDeepCylinder_mass K T, ENNReal.toReal_mul,
    ENNReal.toReal_prod, ENNReal.toReal_prod]
  rfl

theorem sourceKPCoupledDeepCylinder_real_mass_pos (T : Finset (HeightOneSpectrum (𝓞 K))) :
    0 < (sourceKPFiniteStandardHaar K).real (sourceKPCoupledDeepCylinder K T) := by
  rw [sourceKPCoupledDeepCylinder_real_mass K T]
  refine mul_pos (Finset.prod_pos fun P _ => ?_) (Finset.prod_pos fun P _ => ?_)
  · rw [← sourceLocalBall_zero K P]
    exact sourceLocalBall_volume_pos K P 0
  · exact sourceKPDeepIdealImage_volume_pos K P

end
end ArtinMatthews
