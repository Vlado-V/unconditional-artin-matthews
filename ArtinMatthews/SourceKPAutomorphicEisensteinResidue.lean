module

public import ArtinMatthews.SourceKPAutomorphicTruncatedInitial
public import ArtinMatthews.SourceKPAutomorphicResidueDetection
public import ArtinMatthews.SourceEisensteinInitialL2


set_option backward.privateInPublic true
@[expose] public section

/-! The literal general-field Eisenstein residue is nonzero in the genuine automorphic space. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic MeasureTheory Filter
open scoped NumberField AdeleRing MatrixGroups Topology InnerProductSpace
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "L₂" => SourceKPAutomorphicL2 K hζ (sourceKPArchHaar K hζ)
local notation "qf" => Prod.snd (sourceKPCoupledWildWeyl K hζ)
local notation "b" => Prod.snd (sourceKPFiniteLevelMk K hζ (1,qf))
local notation "h₀" => sourceKPAdelicCoverHeight K hζ (1,qf)

theorem sourceKPAutomorphicTruncatedContinuation_ae {T : ℝ} (hT : 1 ≤ T) {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1) :
    ((sourceKPAutomorphicTruncatedContinuation K hζ hT s : L₂) : Y → ℂ) =ᵐ[μY]
      sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s :=
  sourceKPAutomorphicTruncatedContinuation_ae_of_memLp K hζ hT hs
    (sourceKPAutomorphicCompactTruncatedEisenstein_memLp K hζ hs T hT)

theorem sourceKPAutomorphicExceptionalResidue_band {T A B : ℝ}
    (hT : 1 ≤ T) (hTA : 2*T ≤ A) (hA : 1 ≤ A) (hAB : A < B) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      sixthWildPrimes K ⊆ S ∧ sourceHilbertSet K ∅ ⊆ S ∧ traceBadPlaces K ⊆ S ∧
      sourceKPSelectedCuspBandPairing K hζ b (B := B) hA
          (sourceKPAutomorphicExceptionalResidue K hζ hT) =
        sourceKPCoupledScatteringResidue K S * sourceKPSelectedCuspMoment K hζ b A B h₀ (1/6) ∧
      sourceKPSelectedCuspBandPairing K hζ b (B := B) hA
          (sourceKPAutomorphicExceptionalResidue K hζ hT) ≠ 0 :=
  sourceKPAutomorphicExceptionalResidue_band_of_initial K hζ hT hTA hA hAB
    (fun _ hs => sourceKPAutomorphicTruncatedContinuation_ae K hζ hT hs)

theorem sourceKPAutomorphicExceptionalResidue_ne_zero {T : ℝ} (hT : 1 ≤ T) :
    sourceKPAutomorphicExceptionalResidue K hζ hT ≠ 0 := by
  have hA : 1 ≤ 2*T := by linarith
  have hAB : 2*T < 2*T+1 := by linarith
  obtain ⟨_,_,_,_,_,h⟩ := sourceKPAutomorphicExceptionalResidue_band K hζ hT le_rfl hA hAB
  intro hz
  exact h (by rw [hz,map_zero])

theorem sourceKPAutomorphicTruncatedContinuation_order {T : ℝ} (hT : 1 ≤ T) :
    meromorphicOrderAt (sourceKPAutomorphicTruncatedContinuation K hζ hT) (1/6) = -1 :=
  sourceKPAutomorphicTruncatedContinuation_order_of_residue_ne_zero K hζ hT
    (sourceKPAutomorphicExceptionalResidue_ne_zero K hζ hT)

theorem sourceKPAutomorphicExceptionalFormResidue_ne_zero {T : ℝ} (hT : 1 ≤ T) :
    sourceKPAutomorphicExceptionalFormResidue K hζ hT ≠ 0 := by
  intro hz
  apply sourceKPAutomorphicExceptionalResidue_ne_zero K hζ hT
  rw [← sourceKPAutomorphicExceptionalFormResidue_mass K hζ hT,hz,map_zero]

end
end ArtinMatthews
