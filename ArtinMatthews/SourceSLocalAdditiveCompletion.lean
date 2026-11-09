module

public import ArtinMatthews.SourceSLocalAdditiveSupport
public import ArtinMatthews.SourceSLocalExactMeasures


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion IsDedekindDomain
open MeasureTheory Set StandardAdelic
open ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "CPlaces" => {v : InfinitePlace K // IsComplex v}

/-- The product of the literal additive number-field completions. -/
abbrev SLocalAdditiveCompletionSpace := (∀ w : InfinitePlace K, w.Completion) × SFiniteSpace K S

def sourceSLocalCompletionRingEquiv : SLocalAdditiveCompletionSpace K S ≃+* SLocalAdditiveSpace K S :=
  (sourceComplexPlaceAdeleEquiv K).symm.prodCongr (RingEquiv.refl _)

omit [NumberField K] in
private theorem sourceComplexPlaceAdeleEquiv_apply_place
    (a : CPlaces → ℂ) (w : InfinitePlace K) :
    sourceComplexPlaceAdeleEquiv K a w =
      (ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm
        (a ⟨w, IsTotallyComplex.isComplex w⟩) := by
  let hw := IsTotallyComplex.isComplex w
  let e := ringEquivComplexOfIsComplex hw
  apply e.injective
  rw [e.apply_symm_apply]
  exact congrArg (fun x : CPlaces → ℂ => x ⟨w, hw⟩)
    ((sourceComplexPlaceAdeleEquiv K).symm_apply_apply a)

def sourceSLocalCompletionHomeomorph : SLocalAdditiveCompletionSpace K S ≃ₜ SLocalAdditiveSpace K S where
  toEquiv := (sourceSLocalCompletionRingEquiv K S).toEquiv
  continuous_toFun := by
    change Continuous (fun x : SLocalAdditiveCompletionSpace K S =>
      ((sourceComplexPlaceAdeleEquiv K).symm x.1, x.2))
    refine (continuous_pi fun w => ?_).prodMk continuous_snd
    change Continuous (fun x : SLocalAdditiveCompletionSpace K S =>
      ringEquivComplexOfIsComplex w.property (x.1 w.val))
    exact (isometryEquivComplexOfIsComplex w.property).continuous.comp
      ((continuous_apply w.val).comp continuous_fst)
  continuous_invFun := by
    change Continuous (fun x : SLocalAdditiveSpace K S => (sourceComplexPlaceAdeleEquiv K x.1, x.2))
    refine (continuous_pi fun w => ?_).prodMk continuous_snd
    change Continuous (fun x : SLocalAdditiveSpace K S => sourceComplexPlaceAdeleEquiv K x.1 w)
    simp_rw [sourceComplexPlaceAdeleEquiv_apply_place]
    exact (isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm.continuous.comp
      ((continuous_apply (⟨w, IsTotallyComplex.isComplex w⟩ : CPlaces)).comp continuous_fst)

private def sourceSLocalArchAdditiveCoord (w : InfinitePlace K) : w.Completion ≃ᵐ ℂ :=
  (isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).toHomeomorph.toMeasurableEquiv

/-- The trace self-dual measure transported to one literal complex completion. -/
def sourceSLocalArchAdditiveMeasure (w : InfinitePlace K) : Measure w.Completion :=
  Measure.map (sourceSLocalArchAdditiveCoord K w).symm sourceComplexTraceMeasure

def sourceSLocalCompletionMeasure : Measure (SLocalAdditiveCompletionSpace K S) :=
  (Measure.pi (sourceSLocalArchAdditiveMeasure K)).prod (sourceFiniteSelfDualMeasure K S)

def sourceSLocalCompletionMeasurableEquiv :
    SLocalAdditiveCompletionSpace K S ≃ᵐ SLocalAdditiveSpace K S := by
  let (w : InfinitePlace K) : SecondCountableTopology w.Completion := by
    let e := (isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).toHomeomorph
    exact e.isEmbedding.secondCountableTopology
  exact (sourceSLocalCompletionHomeomorph K S).toMeasurableEquiv

theorem sourceSLocalCompletion_measurePreserving :
    MeasurePreserving (sourceSLocalCompletionMeasurableEquiv K S)
      (sourceSLocalCompletionMeasure K S) (sourceSLocalAdditiveMeasure K S) := by
  let i : InfinitePlace K ≃ CPlaces :=
    ⟨fun w => ⟨w, IsTotallyComplex.isComplex w⟩, Subtype.val, fun _ => rfl, fun _ => rfl⟩
  have ha : MeasurePreserving
      (fun (x : ∀ w : InfinitePlace K, w.Completion) w => sourceSLocalArchAdditiveCoord K w (x w))
      (Measure.pi (sourceSLocalArchAdditiveMeasure K))
      (Measure.pi (fun _ : InfinitePlace K => sourceComplexTraceMeasure)) :=
    measurePreserving_pi _ _ fun w =>
      ⟨(sourceSLocalArchAdditiveCoord K w).measurable,
        MeasurableEquiv.map_map_symm (ν := sourceComplexTraceMeasure)
          (sourceSLocalArchAdditiveCoord K w)⟩
  have hi := measurePreserving_piCongrLeft (fun _ : CPlaces => sourceComplexTraceMeasure) i
  have hc : MeasurePreserving (fun x : (∀ w : InfinitePlace K, w.Completion) =>
      (sourceComplexPlaceAdeleEquiv K).symm x) (Measure.pi (sourceSLocalArchAdditiveMeasure K))
      (sourceComplexProductMeasure CPlaces) := hi.comp ha
  let (w : InfinitePlace K) : SigmaFinite (sourceSLocalArchAdditiveMeasure K w) :=
    (sourceSLocalArchAdditiveCoord K w).symm.sigmaFinite_map
  let (p : S) : (sourceLocalSelfDual K p.val).IsAddHaarMeasure := sourceLocalSelfDual_isHaar K p.val
  have : SigmaFinite (sourceComplexProductMeasure CPlaces) := by
    unfold sourceComplexProductMeasure
    infer_instance
  have : SigmaFinite (sourceFiniteSelfDualMeasure K S) := by
    unfold sourceFiniteSelfDualMeasure
    infer_instance
  exact hc.prod (MeasurePreserving.id (sourceFiniteSelfDualMeasure K S))

def sourceSLocalCompletionCharacter (x : SLocalAdditiveCompletionSpace K S) : ℂ :=
  archCharacter K x.1 * ∏ p : S, localFiniteCharacter K p.val (x.2 p)

theorem sourceSLocalCompletionCharacter_eq_coordinate (x : SLocalAdditiveCompletionSpace K S) :
    sourceSLocalCompletionCharacter K S x =
      sourceSLocalAdditiveCharacter K S (sourceSLocalCompletionRingEquiv K S x) := by
  let a : InfiniteAdeleRing K := x.1
  exact congrArg (fun z : InfiniteAdeleRing K => archCharacter K z *
    ∏ p : S, localFiniteCharacter K p.val (x.2 p))
    ((sourceComplexPlaceAdeleEquiv K).apply_symm_apply a).symm

def sourceSLocalCompletionFourier (F : SLocalAdditiveCompletionSpace K S → ℂ)
    (y : SLocalAdditiveCompletionSpace K S) : ℂ :=
  ∫ x, sourceSLocalCompletionCharacter K S (-(x * y)) * F x ∂sourceSLocalCompletionMeasure K S

theorem sourceSLocalCompletionFourier_eq_coordinate
    (F : SLocalAdditiveCompletionSpace K S → ℂ) (y : SLocalAdditiveCompletionSpace K S) :
    sourceSLocalCompletionFourier K S F y =
      sourceSLocalAdditiveFourier K S (F ∘ (sourceSLocalCompletionRingEquiv K S).symm)
        (sourceSLocalCompletionRingEquiv K S y) := by
  let e := sourceSLocalCompletionRingEquiv K S
  let g (x : SLocalAdditiveSpace K S) := sourceSLocalAdditiveCharacter K S (-(x * e y)) * F (e.symm x)
  calc
    _ = ∫ x, g (e x) ∂sourceSLocalCompletionMeasure K S := by
      apply integral_congr_ae
      filter_upwards with x
      rw [sourceSLocalCompletionCharacter_eq_coordinate]
      dsimp only [g]
      rw [e.symm_apply_apply]
      change sourceSLocalAdditiveCharacter K S (e (-(x * y))) * F x = _
      rw [map_neg, map_mul]
    _ = _ := (sourceSLocalCompletion_measurePreserving K S).integral_comp' g

def sourceSLocalCompletionProbe (x : SLocalAdditiveCompletionSpace K S) : ℂ :=
  sourceNumberFieldArchProbe K x.1 * sourceFiniteUnitTest K S x.2

theorem sourceSLocalCompletionProbe_eq_coordinate (x : SLocalAdditiveCompletionSpace K S) :
    sourceSLocalCompletionProbe K S x =
      sourceSLocalAdditiveProbe K S (sourceSLocalCompletionRingEquiv K S x) := rfl

theorem sourceSLocalCompletionProbe_fourier_eq_coordinate (y : SLocalAdditiveCompletionSpace K S) :
    sourceSLocalCompletionFourier K S (sourceSLocalCompletionProbe K S) y =
      sourceSLocalAdditiveFourier K S (sourceSLocalAdditiveProbe K S)
        (sourceSLocalCompletionRingEquiv K S y) := by
  rw [sourceSLocalCompletionFourier_eq_coordinate]
  congr 1
  funext x
  rw [Function.comp_apply, sourceSLocalCompletionProbe_eq_coordinate, RingEquiv.apply_symm_apply]

theorem sourceSLocalCompletionProbe_compactSupport :
    HasCompactSupport (sourceSLocalCompletionProbe K S) :=
  (sourceSLocalAdditiveProbe_compactSupport K S).comp_homeomorph
    (sourceSLocalCompletionHomeomorph K S)

theorem sourceSLocalCompletionProbe_support_away_zero {x : SLocalAdditiveCompletionSpace K S}
    (hx : x ∈ tsupport (sourceSLocalCompletionProbe K S)) :
    (∀ w : InfinitePlace K, x.1 w ≠ 0) ∧ (∀ p : S, x.2 p ≠ 0) := by
  change x ∈ tsupport (sourceSLocalAdditiveProbe K S ∘ sourceSLocalCompletionHomeomorph K S) at hx
  rw [tsupport_comp_eq_preimage] at hx
  have h := sourceSLocalAdditiveProbe_support_away_zero K S hx
  refine ⟨fun w hw => ?_, h.2⟩
  apply h.1 ⟨w, IsTotallyComplex.isComplex w⟩
  change ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w) (x.1 w) = 0
  rw [hw, map_zero]

theorem sourceSLocalCompletionProbe_integrable :
    Integrable (sourceSLocalCompletionProbe K S) (sourceSLocalCompletionMeasure K S) :=
  (sourceSLocalCompletion_measurePreserving K S).integrable_comp_of_integrable
    (sourceSLocalAdditiveProbe_integrable K S)

theorem sourceSLocalCompletionProbe_fourier_integrable :
    Integrable (sourceSLocalCompletionFourier K S (sourceSLocalCompletionProbe K S))
      (sourceSLocalCompletionMeasure K S) :=
  ((sourceSLocalCompletion_measurePreserving K S).integrable_comp_of_integrable
    (sourceSLocalAdditiveProbe_fourier_integrable K S)).congr
      (Filter.Eventually.of_forall fun y => (sourceSLocalCompletionProbe_fourier_eq_coordinate K S y).symm)

theorem sourceSLocalCompletionProbe_fourier_zero :
    sourceSLocalCompletionFourier K S (sourceSLocalCompletionProbe K S) 0 = 0 := by
  rw [sourceSLocalCompletionProbe_fourier_eq_coordinate, map_zero,
    sourceSLocalAdditiveProbe_fourier_zero]

end
end ArtinMatthews.SourcePhysical
