module

public import ArtinMatthews.SourceKPResidualCartesianH1
public import ArtinMatthews.SourceKPResidualCartesianWeak
public import ArtinMatthews.SourceEuclideanNativeEigenSmooth


set_option backward.privateInPublic true
@[expose] public section

/-! A smooth representative of the actual exceptional residue in every full upper chart. -/

namespace ArtinMatthews
open NumberField MeasureTheory Filter SourceHyperbolicGreen HilbertResolvent
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (b : SourceKPFiniteLevelFiber K hζ)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "I" => InfinitePlace K
local notation "X" => ProductSpace I
local notation "E" => EuclideanSpace ℝ (I × Fin 3)
local notation "e" => productFlatEuclideanEquiv I
local notation "Ω" => productUpper I
local notation "ν" => productVolume I
local notation "r" => exceptionalCenter (InfinitePlace.nrComplexPlaces K : ℝ)
local notation "Rform" => sourceKPAutomorphicExceptionalFormResidue K hζ
local notation "Rmass" => sourceKPAutomorphicExceptionalResidue K hζ

theorem sourceKPResidualChart_smooth_rep {T : ℝ} (hT : 1 ≤ T) :
    ∃ f : X → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) f Ω ∧
      f =ᵐ[ν] sourceKPCompactChartPullback K hζ ((Rmass hT).val : Y → ℂ) b := by
  let F := sourceKPCompactChartPullback K hζ ((Rmass hT).val : Y → ℂ) b
  let U : Set E := e '' Ω
  have hU : IsOpen U := (e).toHomeomorph.isOpenMap _ (productUpper_isOpen I)
  have hUpos {z : E} (hz : z ∈ U) : (e).symm z ∈ Ω := by
    obtain ⟨x,hx,rfl⟩ := hz
    simpa only [(e).symm_apply_apply] using hx
  let A : E → H1Vector I →L[ℝ] H1Vector I := productNativeCoefficient ∘ (e).symm
  let d (z : E) : ℂ := ((r * productNativeDensity ((e).symm z) : ℝ) : ℂ)
  have hA : ContDiffOn ℝ (⊤ : ℕ∞) A U := fun z hz =>
    ((productNativeCoefficient_contDiffAt (hUpos hz)).comp z
      (e).symm.contDiff.contDiffAt).contDiffWithinAt
  have hd : ContDiffOn ℝ (⊤ : ℕ∞) d U := by
    intro z hz
    have hρ : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : E => productNativeDensity ((e).symm y)) z :=
      (productNativeDensity_contDiffAt (hUpos hz)).comp z (e).symm.contDiff.contDiffAt
    have hm : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : E => r * productNativeDensity ((e).symm y)) z :=
      (contDiffAt_const : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : E => r) z).mul hρ
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp z hm).contDiffWithinAt
  let equiv := (e).toHomeomorph.toMeasurableEquiv
  have hmp : MeasurePreserving equiv volume volume := productFlatEuclideanEquiv_measurePreserving I
  have hinv : MeasurePreserving equiv.symm volume volume := hmp.symm
  have hsmooth : ∃ f : E → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) f U ∧
      f =ᵐ[(volume : Measure E).restrict U] F ∘ (e).symm := by
    apply sourceLocalEigen_smooth_on_of_native_localization
      (EuclideanSpace.basisFun (I × Fin 3) ℝ) A d (F ∘ (e).symm) hU hA hd
      (fun z _ w => productNativeDiagonal_smul _ _ w)
      (fun z hz => productNativeCoefficient_coercive (hUpos hz))
    intro z hz
    let x := (e).symm z
    let p := sourceKPArchEuclideanUpperMap K x
    obtain ⟨η,W,hW,hp,hηinv,hη⟩ := sourceKPResidualChartPlateau_exists K hζ b p
    let V := sourceKPResidualChartPlateauDomain K hζ b p W
    have hV : IsOpen V := sourceKPResidualChartPlateauDomain_isOpen K hζ b p hW
    have hx : x ∈ V := by
      have h := sourceKPResidualChartPlateauDomain_center K hζ b p hp
      rw [sourceKPArchUpperEuclideanMap_right_inverse K x (fun i => productUpper_pos (hUpos hz) i)] at h
      exact h
    have hVu : V ⊆ Ω :=
      Set.inter_subset_left.trans (sourceKPFiniteChartCoordinateDomain_upper K hζ b p)
    let VE : Set E := e '' V
    have hVE : IsOpen VE := (e).toHomeomorph.isOpenMap _ hV
    have hzV : z ∈ VE := ⟨x,hx,(e).apply_symm_apply z⟩
    let S := tsupport η.val.val
    have hVS : V ⊆ S := sourceKPResidualChartPlateauDomain_support K hζ b p η W hη
    obtain ⟨w,m,g,hw,hwg,hmg⟩ :=
      sourceKPCompactH1Localization_cartesian K hζ b p η (Rform hT).val
    have hmgV := (ae_restrict_iff' hV.measurableSet).mpr
      (hmg.mono (fun _ h hx => h (hVS hx)))
    obtain ⟨c,_,hdom⟩ := productVolume_volume_restrict_le_smul η.val.prop.2.1 η.val.prop.2.2
    have hac : (volume : Measure X).restrict S ≪ ν :=
      Measure.absolutelyContinuous_of_le_smul hdom
    have hmassν := sourceKPResidualLocalizedMass_ae_plateau K hζ b p hT η hW hη
    have hmass := ae_restrict_of_ae_restrict_of_subset hVS (hmassν.filter_mono hac.ae_le)
    have hmV : ∀ᵐ x ∂(volume : Measure X).restrict V, m (e x) = F x := by
      filter_upwards [hmgV, hmass, ae_restrict_mem hV.measurableSet] with y h₁ h₂ hy
      exact h₁.1.trans (h₂ hy)
    refine ⟨VE,hVE,hzV,Set.image_mono hVu,w,m,g,hw,hwg,?_,?_⟩
    · apply (ae_restrict_iff' hVE.measurableSet).mpr
      filter_upwards [hinv.quasiMeasurePreserving.ae ((ae_restrict_iff' hV.measurableSet).mp hmV)]
        with y hy hyV
      obtain ⟨y',hy',rfl⟩ := hyV
      change m (e y') = F ((e).symm (e y'))
      have h := hy (show (e).symm (e y') ∈ V by rwa [(e).symm_apply_apply])
      change m (e ((e).symm (e y'))) = F ((e).symm (e y')) at h
      simpa only [(e).symm_apply_apply] using h
    · exact sourceKPResidualLocalized_cartesian_weak K hζ b p hT η hηinv hW hη m g hmgV

  obtain ⟨f,hf,hfe⟩ := hsmooth
  refine ⟨f ∘ e, hf.comp (e).contDiff.contDiffOn (fun x hx => ⟨x,hx,rfl⟩), ?_⟩
  have h := hmp.quasiMeasurePreserving.ae ((ae_restrict_iff' hU.measurableSet).mp hfe)
  have hF : f ∘ e =ᵐ[(volume : Measure X).restrict Ω] F := by
    refine (ae_restrict_iff' (productUpper_isOpen I).measurableSet).mpr ?_
    filter_upwards [h] with x hx hxΩ
    change f (e x) = F x
    have hx' := hx (show e x ∈ U from ⟨x,hxΩ,rfl⟩)
    change f (e x) = F ((e).symm (e x)) at hx'
    simpa only [(e).symm_apply_apply] using hx'
  rw [productVolume_eq_density]
  exact (withDensity_absolutelyContinuous _ _).ae_eq hF

end
end ArtinMatthews
