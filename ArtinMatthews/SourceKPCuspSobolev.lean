module

public import ArtinMatthews.SourceKPCuspPoincare
public import ArtinMatthews.UnitTorusRellich


set_option backward.privateInPublic true
@[expose] public section

/-! The closed weak-H1 form and Rellich compactness on the actual principal cusp torus. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain Module Module.Free MeasureTheory Topology Set
open scoped NumberField Classical ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] (d : 𝓞 K)
local notation "Q" => SourceKPCuspPrincipalQuotient K d
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local instance : MeasurableSpace Q := borel Q
local instance : BorelSpace Q := ⟨rfl⟩

abbrev SourceKPCuspL2 := Lp ℂ 2 (sourceKPCuspTraceHaar K d)

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12) (hd : d ≠ 0)

def sourceKPCuspL2Coordinates (hζ : IsPrimitiveRoot ζ 12) (hd : d ≠ 0) : SourceKPCuspL2 K d ≃ₗᵢ[ℂ] UnitTorusL2 I := by
  let e := sourceKPCuspPrincipalTorusHomeomorph K d hd
  let he := sourceKPCuspPrincipalTorus_measurePreserving K d hζ hd
  let hi := sourceKPCuspPrincipalTorus_symm_measurePreserving K d hζ hd
  apply LinearIsometryEquiv.ofSurjective (Lp.compMeasurePreservingₗᵢ ℂ e.symm hi)
  intro f
  refine ⟨Lp.compMeasurePreserving e he f, ?_⟩
  change Lp.compMeasurePreserving e.symm hi (Lp.compMeasurePreserving e he f) = f
  apply Lp.ext
  have h1 := Lp.coeFn_compMeasurePreserving (Lp.compMeasurePreserving e he f) hi
  have h2 := hi.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving f he)
  filter_upwards [h1, h2] with x hx hy
  exact hx.trans (hy.trans (congrArg f (e.apply_symm_apply x)))

lemma sourceKPCuspL2Coordinates_coe (f : SourceKPCuspL2 K d) :
    sourceKPCuspL2Coordinates K d hζ hd f =ᵐ[unitTorusHaar I]
      f ∘ (sourceKPCuspPrincipalTorusHomeomorph K d hd).symm :=
  Lp.coeFn_compMeasurePreserving f (sourceKPCuspPrincipalTorus_symm_measurePreserving K d hζ hd)

lemma sourceKPCuspL2Coordinates_integral (f : SourceKPCuspL2 K d) :
    (∫ x, sourceKPCuspL2Coordinates K d hζ hd f x ∂unitTorusHaar I) =
      ∫ x, f x ∂sourceKPCuspTraceHaar K d := by
  rw [integral_congr_ae (sourceKPCuspL2Coordinates_coe K d hζ hd f)]
  exact (sourceKPCuspPrincipalTorus_symm_measurePreserving K d hζ hd).integral_comp
    (sourceKPCuspPrincipalTorusHomeomorph K d hd).symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding f

lemma sourceKPCuspL2Coordinates_integral_norm (f : SourceKPCuspL2 K d) :
    (∫ x, ‖sourceKPCuspL2Coordinates K d hζ hd f x‖ ^ 2 ∂unitTorusHaar I) =
      ∫ x, ‖f x‖ ^ 2 ∂sourceKPCuspTraceHaar K d := by
  calc
    _ = ∫ x, ‖f ((sourceKPCuspPrincipalTorusHomeomorph K d hd).symm x)‖ ^ 2 ∂unitTorusHaar I := by
      apply integral_congr_ae
      filter_upwards [sourceKPCuspL2Coordinates_coe K d hζ hd f] with x hx
      exact congrArg (fun z : ℂ => ‖z‖ ^ 2) hx
    _ = _ := (sourceKPCuspPrincipalTorus_symm_measurePreserving K d hζ hd).integral_comp
      (sourceKPCuspPrincipalTorusHomeomorph K d hd).symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding
      (fun x => ‖f x‖ ^ 2)

def SourceKPCuspWeakGradient (hζ : IsPrimitiveRoot ζ 12) (hd : d ≠ 0) (f : SourceKPCuspL2 K d) (g : I → SourceKPCuspL2 K d) : Prop :=
  UnitTorusWeakGradient I (sourceKPCuspL2Coordinates K d hζ hd f)
    (fun i => sourceKPCuspL2Coordinates K d hζ hd (g i))

def sourceKPCuspContinuousL2 (hζ : IsPrimitiveRoot ζ 12) (hd : d ≠ 0)
    (f : C(Q, ℂ)) : SourceKPCuspL2 K d :=
  (sourceKPCuspL2Coordinates K d hζ hd).symm
    ((sourceKPCuspCoordinatePullback K d hd f).toLp 2 (unitTorusHaar I) ℂ)

lemma sourceKPCuspL2Coordinates_continuous (f : C(Q, ℂ)) :
    sourceKPCuspL2Coordinates K d hζ hd (sourceKPCuspContinuousL2 K d hζ hd f) =
      (sourceKPCuspCoordinatePullback K d hd f).toLp 2 (unitTorusHaar I) ℂ :=
  (sourceKPCuspL2Coordinates K d hζ hd).apply_symm_apply _

lemma sourceKPCuspContinuousL2_coe (f : C(Q, ℂ)) :
    sourceKPCuspContinuousL2 K d hζ hd f =ᵐ[sourceKPCuspTraceHaar K d] f := by
  let e := sourceKPCuspPrincipalTorusHomeomorph K d hd
  have h1 := sourceKPCuspL2Coordinates_coe K d hζ hd (sourceKPCuspContinuousL2 K d hζ hd f)
  rw [sourceKPCuspL2Coordinates_continuous] at h1
  have h2 := ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞)) (𝕜 := ℂ) (unitTorusHaar I)
    (sourceKPCuspCoordinatePullback K d hd f)
  have he : (fun x => sourceKPCuspContinuousL2 K d hζ hd f (e.symm x)) =ᵐ[unitTorusHaar I]
      (fun x => f (e.symm x)) := h1.symm.trans h2
  have hb := (sourceKPCuspPrincipalTorus_measurePreserving K d hζ hd).quasiMeasurePreserving.ae he
  filter_upwards [hb] with x hx
  simpa only [e, ContinuousAddEquiv.symm_apply_apply] using hx

lemma sourceKPCuspWeakGradient_of_directionalDerivative
    (f : C(Q, ℂ)) (g : I → C(Q, ℂ))
    (hfg : SourceKPCuspDirectionalDerivative K d hd f g) :
    SourceKPCuspWeakGradient K d hζ hd
      (sourceKPCuspContinuousL2 K d hζ hd f)
      (fun i => sourceKPCuspContinuousL2 K d hζ hd (g i)) := by
  unfold SourceKPCuspWeakGradient
  simp_rw [sourceKPCuspL2Coordinates_continuous]
  exact unitTorusWeakGradient_of_coordinate_derivative I _ _
    (sourceKPCuspDirectionalDerivative_coordinates K d hd f g hfg)

lemma sourceKPCuspWeakGradient_isClosed :
    IsClosed {fg : SourceKPCuspL2 K d × (I → SourceKPCuspL2 K d) |
      SourceKPCuspWeakGradient K d hζ hd fg.1 fg.2} := by
  let T : SourceKPCuspL2 K d × (I → SourceKPCuspL2 K d) →
      UnitTorusL2 I × (I → UnitTorusL2 I) :=
    fun fg => (sourceKPCuspL2Coordinates K d hζ hd fg.1,
      fun i => sourceKPCuspL2Coordinates K d hζ hd (fg.2 i))
  change IsClosed (T ⁻¹' {fg | UnitTorusWeakGradient I fg.1 fg.2})
  apply (unitTorusWeakGradient_isClosed I).preimage
  exact ((sourceKPCuspL2Coordinates K d hζ hd).continuous.comp continuous_fst).prodMk
    (continuous_pi fun i => (sourceKPCuspL2Coordinates K d hζ hd).continuous.comp
      ((continuous_apply i).comp continuous_snd))

theorem sourceKPCuspWeakGradient_poincare
    (f : SourceKPCuspL2 K d) (g : I → SourceKPCuspL2 K d)
    (hfg : SourceKPCuspWeakGradient K d hζ hd f g)
    (hmean : (∫ x, f x ∂sourceKPCuspTraceHaar K d) = 0) :
    (2 * Real.pi) ^ 2 * (∫ x, ‖f x‖ ^ 2 ∂sourceKPCuspTraceHaar K d) ≤
      ∑ i, ∫ x, ‖g i x‖ ^ 2 ∂sourceKPCuspTraceHaar K d := by
  have hm : (∫ x, sourceKPCuspL2Coordinates K d hζ hd f x ∂unitTorusHaar I) = 0 :=
    (sourceKPCuspL2Coordinates_integral K d hζ hd f).trans hmean
  simpa only [sourceKPCuspL2Coordinates_integral_norm] using
    unitTorusWeakGradient_poincare I _ _ hfg hm

def sourceKPCuspH1EnergySublevel (hζ : IsPrimitiveRoot ζ 12) (hd : d ≠ 0) (R : ℝ) : Set (SourceKPCuspL2 K d) :=
  {f | ∃ g : I → SourceKPCuspL2 K d, SourceKPCuspWeakGradient K d hζ hd f g ∧
    ‖f‖ ^ 2 + ∑ i, ‖g i‖ ^ 2 ≤ R}

lemma sourceKPCuspH1EnergySublevel_coordinates (R : ℝ) :
    sourceKPCuspH1EnergySublevel K d hζ hd R =
      (sourceKPCuspL2Coordinates K d hζ hd) ⁻¹' unitTorusH1EnergySublevel I R := by
  let e := sourceKPCuspL2Coordinates K d hζ hd
  ext f
  constructor
  · rintro ⟨g, hfg, hg⟩
    exact ⟨fun i => e (g i), hfg, by simpa only [LinearIsometryEquiv.norm_map] using hg⟩
  · rintro ⟨g, hfg, hg⟩
    refine ⟨fun i => e.symm (g i), ?_, ?_⟩
    · simpa only [SourceKPCuspWeakGradient, e, LinearIsometryEquiv.apply_symm_apply] using hfg
    · simpa only [LinearIsometryEquiv.norm_map] using hg

theorem sourceKPCuspH1EnergySublevel_isCompact_closure (R : ℝ) :
    IsCompact (closure (sourceKPCuspH1EnergySublevel K d hζ hd R)) := by
  rw [sourceKPCuspH1EnergySublevel_coordinates]
  change IsCompact (closure ((sourceKPCuspL2Coordinates K d hζ hd).toHomeomorph ⁻¹'
    unitTorusH1EnergySublevel I R))
  rw [← (sourceKPCuspL2Coordinates K d hζ hd).toHomeomorph.preimage_closure]
  exact (sourceKPCuspL2Coordinates K d hζ hd).toHomeomorph.isCompact_preimage.mpr
    (unitTorusH1EnergySublevel_isCompact_closure I R)

end
end ArtinMatthews
