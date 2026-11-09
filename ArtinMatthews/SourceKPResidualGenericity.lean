module

public import ArtinMatthews.SourceKPCuspResidualDualProfile
public import ArtinMatthews.SourceKPCuspIntegerResidualMode
public import ArtinMatthews.SourceKPCuspNativeArchInvariance
public import ArtinMatthews.SourceKPResidualUpperObstruction


set_option backward.privateInPublic true
@[expose] public section

/-! All nonzero trace-dual modes of the actual residue cannot vanish:
Fourier completeness would force the upper invariance excluded by genuineness. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain Module.Free MeasureTheory
open scoped NumberField MatrixGroups AdeleRing ENNReal nonZeroDivisors

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)

theorem sourceKPCuspNativeNonzeroModesVanish_residue_of_values_zero
    (d : 𝓞 K) (hd : d ≠ 0) (qf : Gf) (hperiod : sourceKPCuspNativeFinitePeriod K hζ d qf)
    {T : ℝ} (hT : 1 ≤ T) (hz : ∀ m : Kˣ, sourceKPCuspResidualFourierValue K hζ m hT qf = 0) :
    sourceKPCuspNativeNonzeroModesVanish K hζ d hd qf
      (fun z => (sourceKPAutomorphicExceptionalResidue K hζ hT).val z) := by
  intro B hB hpos n hn
  let m : Kˣ := Units.mk0 (sourceKPCuspTraceFrequency K d n)
    (sourceKPCuspTraceFrequency_ne_zero K d hd hn)
  have hdual : (m:K) ∈ FractionalIdeal.dual ℤ ℚ
      ((Ideal.span ({d} : Set (𝓞 K)) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :=
    sourceKPCuspTraceFrequency_mem_dual K d n
  have hprofile := sourceKPCuspResidualFourierCell_ae_eq_value_of_dual K hζ d hd qf
    hperiod m hdual B hB hpos hT
  filter_upwards [hprofile] with y hy
  rw [sourceKPCuspNativeTraceCellCoeff_residue_eq_traceFrequency K hζ d hd qf hT n y]
  change sourceKPCuspResidualFourierCell K hζ d hd qf (m:K) hT y = 0
  simpa only [hz m, zero_mul] using hy

theorem sourceKPCuspResidualFourierValue_exists_ne_zero
    (P : HeightOneSpectrum (𝓞 K)) {T : ℝ} (hT : 1 ≤ T) :
    ∃ (m : Kˣ) (qf : Gf), sourceKPCuspResidualFourierValue K hζ m hT qf ≠ 0 := by
  by_contra h
  have hz (m : Kˣ) (qf : Gf) : sourceKPCuspResidualFourierValue K hζ m hT qf = 0 := by
    by_contra hm
    exact h ⟨m,qf,hm⟩
  let R : Lp ℂ 2 μY := (sourceKPAutomorphicExceptionalResidue K hζ hT).val
  apply sourceKPAutomorphicExceptionalResidue_not_finite_upper_ae K hζ P hT
  intro u
  refine sourceKPAdelicUpper_ae_of_arch_cover_slice K hζ (R : Y → ℂ) ?_ ((0,u) : 𝔸[K])
  intro v qf
  obtain ⟨d,hd,hperiod⟩ := sourceKPAdelicCuspFiniteLevelPeriod K hζ
    ((1,qf) : SourceKPAdelicProjective K hζ)
  exact sourceKPCuspNative_archCover_ae_of_nonzeroModes_zero K hζ d hd qf hperiod R
    (sourceKPCuspNativeNonzeroModesVanish_residue_of_values_zero K hζ d hd qf
      hperiod hT (fun m => hz m qf)) v

end
end ArtinMatthews
