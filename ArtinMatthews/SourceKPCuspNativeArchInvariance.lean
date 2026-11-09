module

public import ArtinMatthews.SourceKPCuspNativeTraceL2
public import ArtinMatthews.SourceKPCuspArchRepresentative
public import ArtinMatthews.SourceKPCuspHeightAE
public import ArtinMatthews.UnitTorusFourierCompleteness


set_option backward.privateInPublic true
@[expose] public section

/-! Full integer-mode vanishing on the genuine principal cells implies
archimedean upper invariance on the actual native Haar space. -/
namespace ArtinMatthews
open NumberField Module.Free MeasureTheory SourceHyperbolicGreen UnitAddTorus
open scoped NumberField AdeleRing MatrixGroups ENNReal NNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (d : 𝓞 K) (hd : d ≠ 0)
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "V" => InfinitePlace K
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "μ" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "E" => sourceKPCuspProductCoordinates K hζ d hd
local notation "ν" => sourceKPCuspProductHeightMeasure K

/-- Vanishing on every compact positive height band, for the full integer dual. -/
def sourceKPCuspNativeNonzeroModesVanish (qf : SourceKPFiniteAdeleProjective K hζ)
    (W : Y → ℂ) : Prop :=
  ∀ B : Set (V → ℝ), IsCompact B → (∀ y ∈ B, ∀ v, 0 < y v) →
    ∀ k : I → ℤ, k ≠ 0 → ∀ᵐ y ∂(ν).restrict B,
      sourceKPCuspNativeTraceCellCoeff K hζ d hd qf W k y = 0

private theorem nativeTraceSlice_arch_translate
    (qf : SourceKPFiniteAdeleProjective K hζ)
    (hperiod : sourceKPCuspNativeFinitePeriod K hζ d qf)
    (W : Y → ℂ) (y : V → ℝ) (hy : ∀ v, 0 < y v)
    (u : InfiniteAdeleRing K) (x : I → ℝ) :
    sourceKPCuspNativeTraceSlice K hζ d hd qf hperiod W y hy
        (sourceKPCuspPrincipalTorusHomeomorph K d hd (QuotientAddGroup.mk ((u,0) : 𝔸[K])) +
          unitTorusUnitCellProjection I x) =
      W (sourceKPCompactCoordinateProjection K hζ (QuotientGroup.mk qf)
        (sourceKPArchEuclideanAction K hζ (sourceKPAdelicUpperLift K hζ ((u,0) : 𝔸[K])).1
          (E (x,y)))) := by
  let g := (sourceKPAdelicUpperLift K hζ (sourceKPCuspUnitCellAdelicPoint K d hd x)).1 *
    sourceKPCuspHeightSection K hζ y hy
  have hg : sourceKPAdelicUpperLift K hζ (sourceKPCuspUnitCellAdelicPoint K d hd x) *
      (sourceKPCuspHeightSection K hζ y hy,qf) = (g,qf) := by
    refine Prod.ext ?_ ?_
    · rfl
    · change sourceKPFiniteAdeleUpperLift K hζ 0 * qf = qf
      rw [sourceKPFiniteAdeleUpperLift_zero, one_mul]
  have hpoint : sourceKPCuspArchRepresentativeCoordinates K hζ g = E (x,y) :=
    sourceKPCuspArchRepresentativeCoordinates_native K hζ d hd x y hy
  refine (sourceKPCuspNativeTraceSlice_translate K hζ d hd qf hperiod W y hy
    ((u,0) : 𝔸[K]) x).trans ?_
  rw [hg, ← sourceKPCuspArchRepresentativeCoordinates_upper K hζ qf u g, hpoint]

theorem sourceKPCuspNative_upper_ae_of_nonzeroModes_zero
    (qf : SourceKPFiniteAdeleProjective K hζ)
    (hperiod : sourceKPCuspNativeFinitePeriod K hζ d qf)
    (W : Y → ℂ) (hW : MemLp W 2 μ) (hWm : Measurable W)
    (hzero : sourceKPCuspNativeNonzeroModesVanish K hζ d hd qf W)
    (u : InfiniteAdeleRing K) :
    ∀ᵐ p ∂productVolume V,
      W (sourceKPCompactCoordinateProjection K hζ (QuotientGroup.mk qf)
        (sourceKPArchEuclideanAction K hζ (sourceKPAdelicUpperLift K hζ ((u,0) : 𝔸[K])).1 p)) =
      W (sourceKPCompactCoordinateProjection K hζ (QuotientGroup.mk qf) p) := by
  let b : SourceKPFiniteLevelFiber K hζ := QuotientGroup.mk qf
  let F : ProductSpace V → ℂ := W ∘ sourceKPCompactCoordinateProjection K hζ b
  let a := (sourceKPAdelicUpperLift K hζ ((u,0) : 𝔸[K])).1
  let A := sourceKPArchEuclideanAction K hζ a
  let μx : Measure (I → ℝ) := volume
  let t := sourceKPCuspPrincipalTorusHomeomorph K d hd (QuotientAddGroup.mk ((u,0) : 𝔸[K]))
  have hfiber' : ∀ᵐ y ∂ν, ∀ hy : ∀ v, 0 < y v,
      ∀ᵐ x ∂μx, F (A (E (x,y))) = F (E (x,y)) := by
    apply sourceKPCuspProductHeight_ae_of_compact K
    intro B hB hpos
    have hl2 := sourceKPCuspNativeTraceSlice_memLp_ae K hζ d hd qf hperiod W hW B hB hpos
    have hcoeff : ∀ᵐ y ∂(ν).restrict B, ∀ k : I → ℤ, k ≠ 0 →
        sourceKPCuspNativeTraceCellCoeff K hζ d hd qf W k y = 0 :=
      ae_all_iff.mpr fun k => by
        by_cases hk : k = 0
        · exact Filter.Eventually.of_forall fun _ hn => (hn hk).elim
        · exact (hzero B hB hpos k hk).mono fun _ h _ => h
    filter_upwards [hl2, hcoeff] with y hyL2 hyzero hy
    let T := sourceKPCuspNativeTraceSlice K hζ d hd qf hperiod W y hy
    have hT (k : I → ℤ) (hk : k ≠ 0) : mFourierCoeff T k = 0 :=
      (sourceKPCuspNativeTraceSlice_fourierCoeff K hζ d hd qf hperiod W k y hy).trans
        (hyzero k hk)
    have ht := unitTorus_add_left_ae_of_nonzero_fourierCoeff_eq_zero I T (hyL2 hy) hT t
    have hx := unitTorusUnitCellProjection_ae_volume I ht
    filter_upwards [hx] with x h
    have hl : T (t + unitTorusUnitCellProjection I x) = F (A (E (x,y))) :=
      nativeTraceSlice_arch_translate K hζ d hd qf hperiod W y hy u x
    have hr : T (unitTorusUnitCellProjection I x) = F (E (x,y)) :=
      sourceKPCuspNativeTraceSlice_unitCell K hζ d hd qf hperiod W y hy x
    exact hl.symm.trans (h.trans hr)
  have hfiber : ∀ᵐ y ∂ν, ∀ᵐ x ∂μx, F (A (E (x,y))) = F (E (x,y)) := by
    filter_upwards [hfiber', sourceKPCuspProductHeight_ae_positive K] with y h hp
    exact h hp
  have hF : Measurable F := hWm.comp (sourceKPCompactCoordinateProjection_measurable K hζ b)
  have hA : Measurable A := (sourceKPArchEuclideanAction_preserving K hζ a).measurable
  have he : Measurable E := (E).continuous.measurable
  have hp : MeasurableSet {p : (I → ℝ) × (V → ℝ) | F (A (E p)) = F (E p)} :=
    measurableSet_eq_fun (hF.comp (hA.comp he)) (hF.comp he)
  have hj : ∀ᵐ p ∂μx.prod ν, F (A (E p)) = F (E p) :=
    (Measure.ae_prod_iff_ae_ae hp).2 ((Measure.ae_ae_comm hp).2 hfiber)
  obtain ⟨c, _hc, hm⟩ := sourceKPCuspProductCoordinates_map_productVolume K hζ d hd
  have hq : Measure.QuasiMeasurePreserving (E).symm (productVolume V) (μx.prod ν) := by
    refine ⟨(E).symm.continuous.measurable, ?_⟩
    rw [hm]
    exact Measure.smul_absolutelyContinuous
  filter_upwards [hq.ae hj] with p h
  exact (E).apply_symm_apply p ▸ h

/-- The per-finite-fibre archimedean Haar conclusion for the native (L^2)
representative. It applies to each fixed archimedean upper translation. -/
theorem sourceKPCuspNative_archCover_ae_of_nonzeroModes_zero
    (qf : SourceKPFiniteAdeleProjective K hζ)
    (hperiod : sourceKPCuspNativeFinitePeriod K hζ d qf)
    (W : Lp ℂ 2 μ)
    (hzero : sourceKPCuspNativeNonzeroModesVanish K hζ d hd qf W)
    (u : InfiniteAdeleRing K) :
    ∀ᵐ g ∂sourceKPArchHaar K hζ,
      W (sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ
        (sourceKPAdelicUpperLift K hζ ((u,0) : 𝔸[K]) * (g,qf)))) =
      W (sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ (g,qf))) := by
  have h := sourceKPCuspNative_upper_ae_of_nonzeroModes_zero K hζ d hd qf hperiod W
    (Lp.memLp W) (Lp.stronglyMeasurable W).measurable hzero u
  have hmp := sourceKPCuspArchRepresentativeCoordinates_measurePreserving K hζ
  filter_upwards [hmp.quasiMeasurePreserving.ae h] with g hg
  simpa only [sourceKPCuspArchRepresentativeCoordinates_upper K hζ qf u g,
    sourceKPCuspArchRepresentativeCoordinates_compact K hζ qf g] using hg

end
end ArtinMatthews
