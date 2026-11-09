module

public import ArtinMatthews.SourceKPTraceJacquetUnfolding
public import ArtinMatthews.SourceFiniteIntertwinerIntegrable


set_option backward.privateInPublic true
@[expose] public section

/-! The actual negative trace character and the compact section
separate into archimedean and finite factors. The finite integral is
the original coupled section on the finite adelic group. -/

namespace ArtinMatthews
open NumberField MeasureTheory StandardAdelic Matrix
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance sourceKPTraceJacquetSplitAdelicMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance sourceKPTraceJacquetSplitAdelicBorel : BorelSpace 𝔸[K] := ⟨rfl⟩
local instance sourceKPTraceJacquetSplitFiniteMeasurable : MeasurableSpace 𝔸ᶠ[K] := borel 𝔸ᶠ[K]
local instance sourceKPTraceJacquetSplitFiniteBorel : BorelSpace 𝔸ᶠ[K] := ⟨rfl⟩
local instance sourceKPTraceJacquetSplitCompletionMeasurable (v : InfinitePlace K) :
    MeasurableSpace v.Completion := borel v.Completion
local instance sourceKPTraceJacquetSplitInfiniteMeasurable : MeasurableSpace (InfiniteAdeleRing K) :=
  inferInstanceAs (MeasurableSpace (∀ v : InfinitePlace K, v.Completion))

def sourceKPTraceJacquetArchCharacter (m : Kˣ) (x : InfiniteAdeleRing K) : ℂ :=
  star (archCharacter K (algebraMap K (InfiniteAdeleRing K) (m : K) * x))

def sourceKPTraceJacquetFiniteCharacter (m : Kˣ) (x : 𝔸ᶠ[K]) : ℂ :=
  star (finiteCharacter K (algebraMap K 𝔸ᶠ[K] (m : K) * x))

theorem sourceKPTraceJacquetCharacter_arch_finite (m : Kˣ) (y : 𝔸[K]) :
    sourceKPTraceJacquetCharacter K m y =
      sourceKPTraceJacquetArchCharacter K m y.1 * sourceKPTraceJacquetFiniteCharacter K m y.2 := by
  change star (archCharacter K (algebraMap K (InfiniteAdeleRing K) (m : K) * y.1) *
      finiteCharacter K (algebraMap K 𝔸ᶠ[K] (m : K) * y.2)) = _
  exact star_mul' _ _

def sourceKPTraceJacquetArchKernel (m : Kˣ) (s : ℂ)
    (g : PGL(2, InfiniteAdeleRing K)) (x : InfiniteAdeleRing K) : ℂ :=
  sourceKPTraceJacquetArchCharacter K m x * sourceKPArchIntertwiningKernel K hζ s g x

def sourceKPTraceJacquetFiniteKernel (m : Kˣ) (s : ℂ)
    (g : SourceKPFiniteAdeleProjective K hζ) (x : 𝔸ᶠ[K]) : ℂ :=
  sourceKPTraceJacquetFiniteCharacter K m x * sourceKPFiniteIntertwiningKernel K hζ s g x

theorem sourceKPAdelicTraceJacquetKernel_arch_finite (m : Kˣ) (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (y : 𝔸[K]) :
    sourceKPAdelicTraceJacquetKernel K hζ m s g y =
      sourceKPTraceJacquetArchKernel K hζ m s g.1 y.1 *
        sourceKPTraceJacquetFiniteKernel K hζ m s g.2 y.2 := by
  unfold sourceKPAdelicTraceJacquetKernel sourceKPTraceJacquetArchKernel sourceKPTraceJacquetFiniteKernel
  rw [sourceKPTraceJacquetCharacter_arch_finite, sourceKPAdelicIntertwiningKernel_arch_finite]
  ring

theorem sourceKPTraceJacquetFiniteKernel_integrable {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (m : Kˣ) (g : SourceKPFiniteAdeleProjective K hζ) :
    Integrable (sourceKPTraceJacquetFiniteKernel K hζ m s g) (sourceKPFiniteStandardHaar K) := by
  have hc : Continuous (sourceKPTraceJacquetFiniteCharacter K m) :=
    continuous_star.comp ((finiteCharacter_continuous K).comp (continuous_const.mul continuous_id))
  refine (sourceKPFiniteIntertwiningKernel_integrable K hζ hs g).bdd_mul
    (c := 1) hc.aestronglyMeasurable ?_
  filter_upwards with x
  simp only [sourceKPTraceJacquetFiniteCharacter, norm_star, finiteCharacter_unitary, le_refl]

theorem sourceKPAdelicCompactEisenstein_traceJacquet_arch_finite {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (m : Kˣ) (g : SourceKPAdelicProjective K hζ) :
    (∫ y in sourceKPAdelicFundamentalDomain K,
      sourceKPTraceJacquetCharacter K m y *
        sourceKPAdelicCompactEisenstein K hζ s (sourceKPAdelicUpperLift K hζ y*g)
      ∂sourceKPAdelicTraceProduct K) =
      (∫ x, sourceKPTraceJacquetArchKernel K hζ m s g.1 x ∂sourceKPArchSelfDualProduct K) *
        ∫ y, sourceKPTraceJacquetFiniteKernel K hζ m s g.2 y ∂sourceKPFiniteStandardHaar K := by
  rw [sourceKPAdelicCompactEisenstein_traceJacquet K hζ hs m g]
  simp_rw [sourceKPAdelicTraceJacquetKernel_arch_finite K hζ m s g]
  exact sourceKPTraceProduct_integral_separated K hζ _ _

end
end ArtinMatthews
