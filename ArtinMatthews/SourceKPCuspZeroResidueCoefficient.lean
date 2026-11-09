module

public import ArtinMatthews.SourceKPCuspZeroResidueTest
public import ArtinMatthews.SourceKPCuspResidualFourierIntegral
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Module.Free MeasureTheory StandardAdelic SourceHyperbolicGreen
open scoped NumberField AdeleRing MatrixGroups Topology NNReal ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "V" => InfinitePlace K

/-- The fixed-set identity keeps the original scattering window available
for simultaneous comparison of several finite fibres. -/
theorem sourceKPCuspResidualZeroCell_ae_eq
    (d : 𝓞 K) (hd : d ≠ 0) (qf : SourceKPFiniteAdeleProjective K hζ)
    (hperiod : ∀ t ∈ sourceKPCuspFiniteIdeal K d,
      ∃ k : sourceKPFiniteDeepMatrixGroup K,
        (1,qf)⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t) * (1,qf) =
          sourceKPFiniteDeepCoverLift K hζ k)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (hM : ∀ s : ℂ, ((3*(Module.finrank ℚ K+1):ℕ):ℝ) ≤ 2*s.re+1 →
      sourceKPAdelicTraceIntertwiner K hζ s (1,qf) =
        sourceKPFiniteFiberScatteringContinuation K hζ qf S s)
    {T : ℝ} (hT : 1 ≤ T) (B : Set (V → ℝ)) (hB : IsCompact B)
    (hpos : ∀ y ∈ B, ∀ v, 0 < y v) :
    sourceKPCuspResidualFourierCell K hζ d hd qf (0:K) hT =ᵐ[
        (sourceKPCuspProductHeightMeasure K).restrict B]
      fun y => sourceKPFiniteFiberScatteringResidue K hζ qf S *
        ((sourceKPCuspArchHeight K y ^ (1/3:ℝ) : ℝ) : ℂ) := by
  obtain ⟨c,hc,hmap⟩ := sourceKPCuspProductCoordinates_map_productVolume K hζ d hd
  let a := sourceKPFiniteFiberScatteringResidue K hζ qf S
  let f := sourceKPCuspResidualFourierCell K hζ d hd qf (0:K) hT
  let g := sourceKPCuspArchPower K (-(1/6:ℂ))
  have hInt (C : Set (V → ℝ)) (hC : IsCompact C)
      (hp : ∀ y ∈ C, ∀ v, 0 < y v) :
      (∫ y in C, f y ∂sourceKPCuspProductHeightMeasure K) =
        a * sourceKPCuspPowerMoment K C (-(1/6:ℂ)) := by
    have hcC : (c:ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    apply mul_left_cancel₀ hcC
    rw [← sourceKPCuspNativeFourierResidue_cell_integral K hζ d hd qf C hC hp (0:K) hT c hc hmap]
    simpa only [a,mul_assoc] using
      sourceKPCuspNativeZeroResidue_eq K hζ d hd qf hperiod c hc hmap S hM C hC hp hT
  have hf : IntegrableOn f B (sourceKPCuspProductHeightMeasure K) :=
    sourceKPCuspResidualFourierCell_integrableOn K hζ d hd qf B hB hpos (0:K) hT
  have hg : IntegrableOn g B (sourceKPCuspProductHeightMeasure K) :=
    sourceKPCuspArchPower_integrableOn K hζ d hd (-(1/6:ℂ)) B hB hpos
  have hz : (fun y => f y-a*g y) =ᵐ[(sourceKPCuspProductHeightMeasure K).restrict B] 0 := by
    apply ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero (hf.sub (hg.const_mul a))
    intro C hC
    rw [Measure.restrict_restrict hC.measurableSet]
    have hCB : IsCompact (C ∩ B) := hC.inter_right hB.isClosed
    have hp : ∀ y ∈ C ∩ B, ∀ v, 0 < y v := fun y hy => hpos y hy.2
    have hfCB := sourceKPCuspResidualFourierCell_integrableOn K hζ d hd qf (C ∩ B) hCB hp (0:K) hT
    have hgCB := sourceKPCuspArchPower_integrableOn K hζ d hd (-(1/6:ℂ)) (C ∩ B) hCB hp
    change (∫ y in C ∩ B, f y-a*g y ∂sourceKPCuspProductHeightMeasure K) = 0
    rw [integral_sub hfCB (hgCB.const_mul a), integral_const_mul]
    exact sub_eq_zero.mpr (hInt (C ∩ B) hCB hp)
  filter_upwards [hz,ae_restrict_mem hB.measurableSet] with y hy hyB
  rw [← sourceKPCuspArchPower_residue K y (hpos y hyB)]
  exact sub_eq_zero.mp hy

/-- One actual finite set works for all cutoffs and all independent height shapes. -/
theorem sourceKPCuspResidualZeroCell_profile
    (d : 𝓞 K) (hd : d ≠ 0) (qf : SourceKPFiniteAdeleProjective K hζ)
    (hperiod : ∀ t ∈ sourceKPCuspFiniteIdeal K d,
      ∃ k : sourceKPFiniteDeepMatrixGroup K,
        (1,qf)⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t) * (1,qf) =
          sourceKPFiniteDeepCoverLift K hζ k)
    (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
      S₀ ⊆ S ∧ sourceHilbertSet K ∅ ⊆ S ∧ traceBadPlaces K ⊆ S ∧
      ∀ (T : ℝ) (hT : 1 ≤ T) (B : Set (V → ℝ)) (hB : IsCompact B)
        (hpos : ∀ y ∈ B, ∀ v, 0 < y v),
        sourceKPCuspResidualFourierCell K hζ d hd qf (0:K) hT =ᵐ[
            (sourceKPCuspProductHeightMeasure K).restrict B]
          fun y => sourceKPFiniteFiberScatteringResidue K hζ qf S *
            ((sourceKPCuspArchHeight K y ^ (1/3:ℝ) : ℝ) : ℂ) := by
  obtain ⟨S,hS,hH,hbad,hM,_,_⟩ := sourceKPFiniteFiberScatteringContinuation_exists K hζ qf S₀
  exact ⟨S,hS,hH,hbad,fun T hT B hB hpos =>
    sourceKPCuspResidualZeroCell_ae_eq K hζ d hd qf hperiod S hM hT B hB hpos⟩

/-- The principal period and the finite scattering set are both actual
choices depending only on the fixed finite fibre and the required bad set. -/
theorem sourceKPCuspResidualZeroCell_has_profile
    (qf : SourceKPFiniteAdeleProjective K hζ)
    (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    ∃ (d : 𝓞 K) (hd : d ≠ 0) (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))),
      S₀ ⊆ S ∧ sourceHilbertSet K ∅ ⊆ S ∧ traceBadPlaces K ⊆ S ∧
      ∀ (T : ℝ) (hT : 1 ≤ T) (B : Set (V → ℝ)) (hB : IsCompact B)
        (hpos : ∀ y ∈ B, ∀ v, 0 < y v),
        sourceKPCuspResidualFourierCell K hζ d hd qf (0:K) hT =ᵐ[
            (sourceKPCuspProductHeightMeasure K).restrict B]
          fun y => sourceKPFiniteFiberScatteringResidue K hζ qf S *
            ((sourceKPCuspArchHeight K y ^ (1/3:ℝ) : ℝ) : ℂ) := by
  obtain ⟨d,hd,_,hp⟩ := sourceKPAdelicCuspFrequencyPeriod K hζ (0:K) (1,qf)
  obtain ⟨S,hS,hH,hbad,h⟩ := sourceKPCuspResidualZeroCell_profile K hζ d hd qf hp S₀
  exact ⟨d,hd,S,hS,hH,hbad,h⟩

end
end ArtinMatthews
