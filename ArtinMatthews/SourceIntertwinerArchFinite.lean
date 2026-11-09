module

public import ArtinMatthews.SourceIntertwinerProductMeasure
public import ArtinMatthews.SourceArchSectionFactorization
public import ArtinMatthews.SourceKPAdelicTraceConstantTerm


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance archFiniteAdelicMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance archFiniteAdelicBorel : BorelSpace 𝔸[K] := ⟨rfl⟩
local instance archFiniteFiniteMeasurable : MeasurableSpace 𝔸ᶠ[K] := borel 𝔸ᶠ[K]
local instance archFiniteFiniteBorel : BorelSpace 𝔸ᶠ[K] := ⟨rfl⟩
local instance archFiniteCompletionMeasurable (v : InfinitePlace K) : MeasurableSpace v.Completion := borel _
local instance archFiniteCompletionBorel (v : InfinitePlace K) : BorelSpace v.Completion := ⟨rfl⟩
local instance archFiniteInfiniteMeasurable : MeasurableSpace (InfiniteAdeleRing K) :=
  inferInstanceAs (MeasurableSpace (∀ v : InfinitePlace K, v.Completion))

def sourceKPArchIntertwiningKernel (s : ℂ) (g : PGL(2, InfiniteAdeleRing K))
    (x : InfiniteAdeleRing K) : ℂ :=
  sourceArchSphericalProduct K hζ s
    ((sourceKPAdelicProjectiveWeyl K hζ).1 *
      ProjGenLinGroup.mk (sourceKPUpperMatrix (InfiniteAdeleRing K) x) * g)

def sourceKPFiniteIntertwiningKernel (s : ℂ) (g : SourceKPFiniteAdeleProjective K hζ)
    (x : 𝔸ᶠ[K]) : ℂ :=
  sourceKPAdelicCompactScalar K hζ s
    (1, (sourceKPAdelicProjectiveWeyl K hζ).2 * sourceKPFiniteAdeleUpperLift K hζ x * g)

theorem sourceKPAdelicIntertwiningKernel_arch_finite (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (y : 𝔸[K]) :
    sourceKPAdelicIntertwiningKernel K hζ s g y =
      sourceKPArchIntertwiningKernel K hζ s g.1 y.1 *
        sourceKPFiniteIntertwiningKernel K hζ s g.2 y.2 := by
  change sourceKPAdelicCompactScalar K hζ s
    ((sourceKPAdelicProjectiveWeyl K hζ).1 *
      ProjGenLinGroup.mk (sourceKPUpperMatrix (InfiniteAdeleRing K) y.1) * g.1,
     (sourceKPAdelicProjectiveWeyl K hζ).2 * sourceKPFiniteAdeleUpperLift K hζ y.2 * g.2) = _
  exact sourceArchCompactScalar_factor K hζ s _ _

def sourceKPArchIntertwiner (s : ℂ) (g : PGL(2, InfiniteAdeleRing K)) : ℂ :=
  ∫ x, sourceKPArchIntertwiningKernel K hζ s g x ∂sourceKPArchSelfDualProduct K

def sourceKPFiniteIntertwiner (s : ℂ) (g : SourceKPFiniteAdeleProjective K hζ) : ℂ :=
  ∫ x, sourceKPFiniteIntertwiningKernel K hζ s g x ∂sourceKPFiniteStandardHaar K

theorem sourceKPAdelicTraceIntertwiner_arch_finite (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicTraceIntertwiner K hζ s g =
      sourceKPArchIntertwiner K hζ s g.1 * sourceKPFiniteIntertwiner K hζ s g.2 := by
  unfold sourceKPAdelicTraceIntertwiner sourceKPAdelicIntertwiner
  simp_rw [sourceKPAdelicIntertwiningKernel_arch_finite]
  exact sourceKPTraceProduct_integral_separated K hζ _ _

end
end ArtinMatthews
