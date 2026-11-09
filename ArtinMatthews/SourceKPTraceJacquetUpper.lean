module

public import ArtinMatthews.SourceKPTraceJacquetUnfolding
public import ArtinMatthews.SourceKPIntertwinerRationalKernel


set_option backward.privateInPublic true
@[expose] public section

/-! Exact upper-root covariance of the original normalized trace Jacquet
integral, with the positive phase determined by its negative test character. -/
namespace ArtinMatthews
open NumberField MeasureTheory StandardAdelic
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance sourceTraceJacquetUpperMeasurable : MeasurableSpace 𝔸[K] := borel _
local instance sourceTraceJacquetUpperBorel : BorelSpace 𝔸[K] := ⟨rfl⟩

theorem sourceKPAdelicTraceJacquetKernel_left_upper
    (m : Kˣ) (s : ℂ) (g : SourceKPAdelicProjective K hζ) (x y : 𝔸[K]) :
    sourceKPAdelicTraceJacquetKernel K hζ m s (sourceKPAdelicUpperLift K hζ x*g) y =
      character K (algebraMap K 𝔸[K] (m:K)*x) * sourceKPAdelicTraceJacquetKernel K hζ m s g (y+x) := by
  let z := character K (algebraMap K 𝔸[K] (m:K)*x)
  have hu : z * sourceKPTraceJacquetCharacter K m x = 1 := by
    change z * (starRingEnd ℂ) z = 1
    have hn : ‖z‖ = 1 := character_unitary K _
    rw [Complex.mul_conj',hn]
    norm_num
  have hχ : sourceKPTraceJacquetCharacter K m y = z * sourceKPTraceJacquetCharacter K m (y+x) := by
    rw [sourceKPTraceJacquetCharacter_add]
    calc
      _ = sourceKPTraceJacquetCharacter K m y * 1 := (mul_one _).symm
      _ = sourceKPTraceJacquetCharacter K m y * (z*sourceKPTraceJacquetCharacter K m x) := by rw [hu]
      _ = _ := by ring
  unfold sourceKPAdelicTraceJacquetKernel
  rw [sourceKPAdelicIntertwiningKernel_left_upper,hχ,mul_assoc]

theorem sourceKPAdelicTraceJacquetKernel_integral_left_upper
    (m : Kˣ) (s : ℂ) (g : SourceKPAdelicProjective K hζ) (x : 𝔸[K]) :
    (∫ y, sourceKPAdelicTraceJacquetKernel K hζ m s (sourceKPAdelicUpperLift K hζ x*g) y
      ∂sourceKPAdelicTraceProduct K) =
      character K (algebraMap K 𝔸[K] (m:K)*x) *
        ∫ y, sourceKPAdelicTraceJacquetKernel K hζ m s g y ∂sourceKPAdelicTraceProduct K := by
  let μ := sourceKPAdelicTraceProduct K
  letI : μ.IsAddHaarMeasure := by
    change (sourceKPAdelicTraceProduct K).IsAddHaarMeasure
    rw [sourceKPAdelicTraceProduct_eq_standard_of_primitiveRoot K hζ]
    infer_instance
  simp_rw [sourceKPAdelicTraceJacquetKernel_left_upper K hζ m s g x]
  rw [integral_const_mul,integral_add_right_eq_self]

theorem sourceKPAdelicCompactEisenstein_traceJacquet_left_upper {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (m : Kˣ) (g : SourceKPAdelicProjective K hζ) (x : 𝔸[K]) :
    (∫ y in sourceKPAdelicFundamentalDomain K,
      sourceKPTraceJacquetCharacter K m y *
        sourceKPAdelicCompactEisenstein K hζ s
          (sourceKPAdelicUpperLift K hζ y*(sourceKPAdelicUpperLift K hζ x*g))
      ∂sourceKPAdelicTraceProduct K) =
      character K (algebraMap K 𝔸[K] (m:K)*x) *
        ∫ y in sourceKPAdelicFundamentalDomain K,
          sourceKPTraceJacquetCharacter K m y *
            sourceKPAdelicCompactEisenstein K hζ s (sourceKPAdelicUpperLift K hζ y*g)
          ∂sourceKPAdelicTraceProduct K := by
  rw [sourceKPAdelicCompactEisenstein_traceJacquet K hζ hs m (sourceKPAdelicUpperLift K hζ x*g),
    sourceKPAdelicCompactEisenstein_traceJacquet K hζ hs m g]
  exact sourceKPAdelicTraceJacquetKernel_integral_left_upper K hζ m s g x

end
end ArtinMatthews
