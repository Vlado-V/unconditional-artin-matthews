module

public import ArtinMatthews.SourceKPCuspNativeTraceSlice
public import ArtinMatthews.SourceKPCuspResidualFourierIntegral
public import ArtinMatthews.SourceKPCuspTraceModePhase


set_option backward.privateInPublic true
@[expose] public section

/-! The literal native integer Fourier coefficient of the actual residue is
the raw residual field-frequency coefficient of its trace-dual index. -/
namespace ArtinMatthews
open NumberField Module.Free
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPCuspNativeTraceCellCoeff_residue_eq_traceFrequency
    (d : 𝓞 K) (hd : d ≠ 0) (qf : SourceKPFiniteAdeleProjective K hζ)
    {T : ℝ} (hT : 1 ≤ T) (n : ChooseBasisIndex ℤ (𝓞 K) → ℤ) (y : InfinitePlace K → ℝ) :
    sourceKPCuspNativeTraceCellCoeff K hζ d hd qf
        (fun z => (sourceKPAutomorphicExceptionalResidue K hζ hT).val z) n y =
      sourceKPCuspResidualFourierCell K hζ d hd qf (sourceKPCuspTraceFrequency K d n) hT y := by
  simp only [sourceKPCuspNativeTraceCellCoeff, sourceKPCuspResidualFourierCell,
    sourceKPCuspTraceFrequency_unitCell_star_phase, smul_eq_mul]

end
end ArtinMatthews
