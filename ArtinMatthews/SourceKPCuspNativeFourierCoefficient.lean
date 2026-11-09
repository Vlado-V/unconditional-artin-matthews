module

public import ArtinMatthews.SourceKPCuspNativeUpperPoint


set_option backward.privateInPublic true
@[expose] public section

/-! The actual native horizontal Fourier coefficient of the initial
Eisenstein series is the product of the exact archimedean integral and
the original coupled finite integral. -/
namespace ArtinMatthews
open NumberField Module.Free MeasureTheory StandardAdelic SourceHyperbolicGreen
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (d : 𝓞 K) (hd : d ≠ 0)
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "V" => InfinitePlace K

theorem sourceKPCuspNativeEisenstein_fourier
    (qf : SourceKPFiniteAdeleProjective K hζ)
    (hperiod : ∀ t ∈ sourceKPCuspFiniteIdeal K d,
      ∃ k : sourceKPFiniteDeepMatrixGroup K,
        (1,qf)⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t) * (1,qf) =
          sourceKPFiniteDeepCoverLift K hζ k)
    {s : ℂ} (hs : ((3*(Module.finrank ℚ K+1):ℕ):ℝ) ≤ 2*s.re+1)
    (m : Kˣ) (hm : ∃ r : 𝓞 K, (m:K)*(d:K) = (r:K))
    (y : V → ℝ) (hy : ∀ v, 0 < y v) :
    (∫ x : I → ℝ,
      star (character K (algebraMap K 𝔸[K] (m:K)*sourceKPCuspUnitCellAdelicPoint K d hd x)) *
        sourceKPAutomorphicCompactEisenstein K hζ s
          (sourceKPCompactCoordinateProjection K hζ (QuotientGroup.mk qf)
            (sourceKPCuspProductCoordinates K hζ d hd (x,y)))
      ∂unitTorusUnitCellMeasure I) =
      (∫ z, sourceKPTraceJacquetArchKernel K hζ m s (sourceKPCuspHeightSection K hζ y hy) z
        ∂sourceKPArchSelfDualProduct K) *
        ∫ z, sourceKPTraceJacquetFiniteKernel K hζ m s qf z ∂sourceKPFiniteStandardHaar K := by
  have hp := sourceKPCuspFinitePeriod_arch_change K hζ d qf hperiod (sourceKPCuspHeightSection K hζ y hy)
  have h := sourceKPCuspEisensteinCell_traceJacquet K hζ d
    (sourceKPCuspHeightSection K hζ y hy,qf) hp hs hd m hm
  calc
    _ = ∫ x : I → ℝ,
        star (character K (algebraMap K 𝔸[K] (m:K)*sourceKPCuspUnitCellAdelicPoint K d hd x)) *
          sourceKPAdelicCompactEisenstein K hζ s
            (sourceKPAdelicUpperLift K hζ (sourceKPCuspUnitCellAdelicPoint K d hd x) *
              (sourceKPCuspHeightSection K hζ y hy,qf))
        ∂unitTorusUnitCellMeasure I := by
      apply integral_congr_ae
      filter_upwards with x
      rw [sourceKPCuspNativeUpperPoint_compact,sourceKPAutomorphicCompactEisenstein_adelic]
    _ = _ := h

end
end ArtinMatthews
