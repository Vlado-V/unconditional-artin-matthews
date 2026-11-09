module

public import ArtinMatthews.SourceKPCuspRationalHeight
public import ArtinMatthews.SourceKPTraceJacquetRational
public import ArtinMatthews.SourceKPAutomorphicCompactEisenstein


set_option backward.privateInPublic true
@[expose] public section

/-! Unit-frequency reduction on positive archimedean heights keeps the
literal finite rational translate and removes only the proved compact
phase factor. -/
namespace ArtinMatthews
open NumberField MeasureTheory
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance sourceKPJacquetHeightMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance sourceKPJacquetHeightBorel : BorelSpace 𝔸[K] := ⟨rfl⟩

theorem sourceKPTraceJacquetFundamental_right_deep (s : ℂ) (m : Kˣ)
    (g : SourceKPAdelicProjective K hζ) (k : sourceKPAdelicDeepCompact K hζ) :
    (∫ z in sourceKPAdelicFundamentalDomain K,
      sourceKPTraceJacquetCharacter K m z *
        sourceKPAdelicCompactEisenstein K hζ s (sourceKPAdelicUpperLift K hζ z * (g * k.val))
      ∂sourceKPAdelicTraceProduct K) =
      ∫ z in sourceKPAdelicFundamentalDomain K,
        sourceKPTraceJacquetCharacter K m z *
          sourceKPAdelicCompactEisenstein K hζ s (sourceKPAdelicUpperLift K hζ z * g)
        ∂sourceKPAdelicTraceProduct K := by
  apply integral_congr_ae
  filter_upwards [] with z
  rw [← mul_assoc, sourceKPAdelicCompactEisenstein_right_deep K hζ s _ k]

theorem sourceKPAdelicCompactEisenstein_traceJacquet_positive_height
    {s : ℂ} (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1)
    (m : Kˣ) (y : InfinitePlace K → ℝ) (hy : ∀ v, 0 < y v)
    (qf : SourceKPFiniteAdeleProjective K hζ) :
    (∫ z in sourceKPAdelicFundamentalDomain K,
      sourceKPTraceJacquetCharacter K m z * sourceKPAdelicCompactEisenstein K hζ s
        (sourceKPAdelicUpperLift K hζ z * (sourceKPCuspHeightSection K hζ y hy,qf))
      ∂sourceKPAdelicTraceProduct K) =
      ∫ z in sourceKPAdelicFundamentalDomain K,
        sourceKPTraceJacquetCharacter K 1 z * sourceKPAdelicCompactEisenstein K hζ s
          (sourceKPAdelicUpperLift K hζ z *
            (sourceKPCuspHeightSection K hζ (sourceKPCuspRationalHeight K hζ m y)
                (sourceKPCuspRationalHeight_pos K hζ m y hy),
              (sourceKPAdelicProjectiveRationalLift K hζ (sourceKPProjectiveDiagonalHom K m)).2 * qf))
        ∂sourceKPAdelicTraceProduct K := by
  rw [sourceKPAdelicCompactEisenstein_traceJacquet_rational_diagonal K hζ hs m
    (sourceKPCuspHeightSection K hζ y hy,qf)]
  rw [sourceKPCuspRationalHeight_factor K hζ m y hy qf]
  exact sourceKPTraceJacquetFundamental_right_deep K hζ s 1 _ _

end
end ArtinMatthews
