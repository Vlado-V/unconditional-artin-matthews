module

public import ArtinMatthews.SourceKPCuspRepresentativeFourier
public import ArtinMatthews.SourceKPCuspResidualFourierIntegral
public import ArtinMatthews.SourceKPCompactC2Core


set_option backward.privateInPublic true
@[expose] public section

/-! Transfer the full-dimensional equality of representatives through the
native measure identity, then take horizontal integrals at a.e. height. -/

namespace ArtinMatthews
open NumberField Module.Free MeasureTheory SourceHyperbolicGreen StandardAdelic Set
open scoped NumberField AdeleRing ENNReal NNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (d : 𝓞 K) (hd : d ≠ 0)
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "V" => InfinitePlace K
local notation "X" => ProductSpace V
local notation "E" => sourceKPCuspProductCoordinates K hζ d hd
local notation "P" => sourceKPCuspPositiveHeights K

theorem sourceKPCuspRepresentativeFourierCell_ae_eq_residual
    (qf : SourceKPFiniteAdeleProjective K hζ) (m : K) {T : ℝ} (hT : 1 ≤ T)
    (U : X → ℂ)
    (hUae : U =ᵐ[productVolume V] sourceKPCompactChartPullback K hζ
      (sourceKPAutomorphicExceptionalResidue K hζ hT).val (QuotientGroup.mk qf))
    (B : Set (V → ℝ)) (hB : MeasurableSet B) (hpos : B ⊆ P) :
    sourceKPCuspRepresentativeFourierCell K hζ d hd U m =ᵐ[
        (sourceKPCuspProductHeightMeasure K).restrict B]
      sourceKPCuspResidualFourierCell K hζ d hd qf m hT := by
  let μ := (volume : Measure (I → ℝ))
  let ν := sourceKPCuspProductHeightMeasure K
  let W := sourceKPCompactChartPullback K hζ
    (sourceKPAutomorphicExceptionalResidue K hζ hT).val (QuotientGroup.mk qf)
  let e := (E).symm.toHomeomorph.toMeasurableEquiv
  obtain ⟨c, hc, hmap⟩ := sourceKPCuspProductCoordinates_map_productVolume K hζ d hd
  have hprod : ∀ᵐ p ∂μ.prod ν, U (E p) = W (E p) := by
    have he : ∀ᵐ p ∂Measure.map (E).symm (productVolume V), U (E p) = W (E p) := by
      change ∀ᵐ p ∂Measure.map e (productVolume V), U (E p) = W (E p)
      apply e.measurableEmbedding.ae_map_iff.2
      exact hUae.mono fun z hz => by
        change U (E ((E).symm z)) = W (E ((E).symm z))
        rw [(E).apply_symm_apply]
        exact hz
    have hc' : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
    rw [hmap, Measure.ae_ennreal_smul_measure_eq hc'] at he
    exact he
  have hswap : ∀ᵐ p ∂ν.prod μ, U (E (p.2,p.1)) = W (E (p.2,p.1)) :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae hprod
  have hs : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, U (E (x,y)) = W (E (x,y)) :=
    Measure.ae_ae_of_ae_prod hswap
  have hcell : unitTorusUnitCellMeasure I = μ.restrict (Set.univ.pi fun _ : I => Ioc (0 : ℝ) 1) := by
    symm
    exact Measure.restrict_pi_pi _ _
  change sourceKPCuspRepresentativeFourierCell K hζ d hd U m =ᵐ[ν.restrict B]
    sourceKPCuspResidualFourierCell K hζ d hd qf m hT
  filter_upwards [ae_restrict_of_ae (s := B) hs, ae_restrict_mem hB] with y hy hyB
  rw [sourceKPCuspRepresentativeFourierCell, sourceKPCuspResidualFourierCell]
  apply integral_congr_ae
  rw [hcell]
  exact (ae_restrict_of_ae hy).mono fun x hx => by
    have hxy : E (x,y) ∈ productUpper V := by
      intro v _
      change 0 < E (x,y) v 2
      rw [sourceKPCuspProductCoordinates_height]
      exact hpos hyB v
    have hR : U (E (x,y)) =
        (sourceKPAutomorphicExceptionalResidue K hζ hT).val
          (sourceKPCompactCoordinateProjection K hζ
            (show SourceKPFiniteLevelFiber K hζ from QuotientGroup.mk qf) (E (x,y))) :=
      hx.trans (ite_eq_left hxy)
    exact congrArg (fun z : ℂ => star (character K (algebraMap K 𝔸[K] m *
      sourceKPCuspUnitCellAdelicPoint K d hd x)) * z) hR

end
end ArtinMatthews
