module

public import ArtinMatthews.SourceArchIntertwinerProduct
public import ArtinMatthews.SourceKPAdelicCoordinateIntertwiner


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance coordinateProductAdelicMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance coordinateProductAdelicBorel : BorelSpace 𝔸[K] := ⟨rfl⟩
local instance coordinateProductFiniteMeasurable : MeasurableSpace 𝔸ᶠ[K] := borel 𝔸ᶠ[K]
local instance coordinateProductFiniteBorel : BorelSpace 𝔸ᶠ[K] := ⟨rfl⟩
local instance coordinateProductCompletionMeasurable (v : InfinitePlace K) : MeasurableSpace v.Completion := borel _
local instance coordinateProductCompletionBorel (v : InfinitePlace K) : BorelSpace v.Completion := ⟨rfl⟩
local instance coordinateProductInfiniteMeasurable : MeasurableSpace (InfiniteAdeleRing K) :=
  inferInstanceAs (MeasurableSpace (∀ v : InfinitePlace K, v.Completion))

theorem sourceArchSphericalProduct_eq_scalar (s : ℂ)
    (g : PGL(2, InfiniteAdeleRing K)) :
    sourceArchSphericalProduct K hζ s g =
      sourceKPAdelicCompactScalar K hζ s (g, 1) := by
  rw [sourceArchCompactScalar_factor]
  change _ = _ * sourceKPAdelicCompactScalar K hζ s 1
  rw [sourceKPAdelicCompactScalar_one, mul_one]

theorem sourceArchSphericalProduct_diagonal_mul (s : ℂ)
    (a : (InfiniteAdeleRing K)ˣ) (g : PGL(2, InfiniteAdeleRing K)) :
    sourceArchSphericalProduct K hζ s (sourceKPProjectiveDiagonalHom _ a * g) =
      sourceArchSphericalProduct K hζ s (sourceKPProjectiveDiagonalHom _ a) *
        sourceArchSphericalProduct K hζ s g := by
  let b := sourceKPDiagonalHom (InfiniteAdeleRing K) a
  have hb : b ∈ sourceKPRingNormalizedBorel (InfiniteAdeleRing K) :=
    sourceKPRingNormalizedBorel_diagonal _ a
  have hbase := sourceArchNormalizedBorel_scalar K hζ s b hb 1
  have hprod := sourceArchNormalizedBorel_scalar K hζ s b hb (g, 1)
  simp only [mul_one] at hbase
  simp only [Prod.mk_mul_mk, mul_one] at hprod
  change sourceKPAdelicCompactScalar K hζ s (sourceKPProjectiveDiagonalHom _ a, 1) =
    (sourceKPIdeleComplexNorm K (s + 1 / 2)
      (sourceArchOnlyIdele K (GeneralLinearGroup.det b)) : ℂ) *
        sourceKPAdelicCompactScalar K hζ s 1 at hbase
  rw [sourceKPAdelicCompactScalar_one, mul_one] at hbase
  change sourceKPAdelicCompactScalar K hζ s (sourceKPProjectiveDiagonalHom _ a * g, 1) =
    (sourceKPIdeleComplexNorm K (s + 1 / 2)
      (sourceArchOnlyIdele K (GeneralLinearGroup.det b)) : ℂ) *
        sourceKPAdelicCompactScalar K hζ s (g, 1) at hprod
  simpa only [sourceArchSphericalProduct_eq_scalar, hbase] using hprod

theorem sourceKPAdelicTorus_arch_diagonal (t : sourceKPAdelicCoveringTorus K hζ) :
    ∃ a : (InfiniteAdeleRing K)ˣ,
      t.val.1 = sourceKPProjectiveDiagonalHom (InfiniteAdeleRing K) a := by
  obtain ⟨z, a, ha⟩ := (sourceKPAdelicCoveringTorus_mem_iff K hζ t.val).mp t.property
  refine ⟨sourceKPIdeleInfiniteUnit K a, ?_⟩
  have h := congrArg Prod.fst ha
  change t.val.1 = 1 * sourceKPProjectiveDiagonalHom _ (sourceKPIdeleInfiniteUnit K a) at h
  simpa only [one_mul] using h

def sourceKPFiniteCoordinateIntertwiningKernel (s : ℂ)
    (g t : SourceKPFiniteAdeleProjective K hζ) (x : 𝔸ᶠ[K]) : ℂ :=
  sourceKPAdelicCompactScalar K hζ s
    (1, t * ((sourceKPAdelicProjectiveWeyl K hζ).2 *
      sourceKPFiniteAdeleUpperLift K hζ x * g))

def sourceKPFiniteCoordinateIntertwiner (s : ℂ)
    (g t : SourceKPFiniteAdeleProjective K hζ) : ℂ :=
  ∫ x, sourceKPFiniteCoordinateIntertwiningKernel K hζ s g t x
    ∂sourceKPFiniteStandardHaar K

theorem sourceKPAdelicCoordinateKernel_arch_finite (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (t : sourceKPAdelicCoveringTorus K hζ)
    (y : 𝔸[K]) :
    sourceKPAdelicCoordinateKernel K hζ s g t y =
      (sourceKPAdelicBorelModularHalf K hζ
        (sourceKPAdelicBorelTorusInclusion K hζ t))⁻¹ *
      sourceArchSphericalProduct K hζ s t.val.1 *
      sourceKPArchIntertwiningKernel K hζ s g.1 y.1 *
      sourceKPFiniteCoordinateIntertwiningKernel K hζ s g.2 t.val.2 y.2 := by
  unfold sourceKPAdelicCoordinateKernel
  rw [sourceKPAdelicCompactSection_coordinate]
  change _ * sourceKPAdelicCompactScalar K hζ s
    (t.val.1 * ((sourceKPAdelicProjectiveWeyl K hζ).1 *
      ProjGenLinGroup.mk (sourceKPUpperMatrix (InfiniteAdeleRing K) y.1) * g.1),
     t.val.2 * ((sourceKPAdelicProjectiveWeyl K hζ).2 *
      sourceKPFiniteAdeleUpperLift K hζ y.2 * g.2)) = _
  rw [sourceArchCompactScalar_factor]
  obtain ⟨a, ha⟩ := sourceKPAdelicTorus_arch_diagonal K hζ t
  rw [ha, sourceArchSphericalProduct_diagonal_mul]
  simp only [sourceKPArchIntertwiningKernel, sourceKPFiniteCoordinateIntertwiningKernel,
    mul_assoc]

theorem sourceKPAdelicCoordinateIntegral_arch_finite (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (t : sourceKPAdelicCoveringTorus K hζ) :
    (sourceKPAdelicCoordinateIntegral K hζ (sourceKPAdelicTraceProduct K) s g).val t =
      (sourceKPAdelicBorelModularHalf K hζ
        (sourceKPAdelicBorelTorusInclusion K hζ t))⁻¹ *
      sourceArchSphericalProduct K hζ s t.val.1 *
      sourceKPArchIntertwiner K hζ s g.1 *
      sourceKPFiniteCoordinateIntertwiner K hζ s g.2 t.val.2 := by
  rw [sourceKPAdelicCoordinateIntegral_apply]
  simp_rw [sourceKPAdelicCoordinateKernel_arch_finite]
  simp only [mul_assoc]
  rw [integral_const_mul, integral_const_mul,
    sourceKPTraceProduct_integral_separated K hζ]
  rfl

theorem sourceKPAdelicSphericalIntertwinerValue_arch_finite {s : ℂ} (hs : 0 < s.re)
    (g : SourceKPAdelicProjective K hζ) (t : sourceKPAdelicCoveringTorus K hζ) :
    (sourceKPAdelicSphericalIntertwinerValue K hζ (sourceKPAdelicTraceProduct K) s g).val t =
      (sourceKPAdelicBorelModularHalf K hζ
        (sourceKPAdelicBorelTorusInclusion K hζ
          (sourceKPAdelicCoveringTorusWeyl K hζ t)))⁻¹ *
      sourceArchSphericalProduct K hζ s (sourceKPAdelicCoveringTorusWeyl K hζ t).val.1 *
      (((Real.pi : ℂ) / s) ^ Fintype.card (InfinitePlace K) *
        sourceArchSphericalProduct K hζ (-s) g.1) *
      sourceKPFiniteCoordinateIntertwiner K hζ s g.2
        (sourceKPAdelicCoveringTorusWeyl K hζ t).val.2 := by
  change (sourceKPAdelicCoordinateIntegral K hζ (sourceKPAdelicTraceProduct K) s g).val
    (sourceKPAdelicCoveringTorusWeyl K hζ t) = _
  rw [sourceKPAdelicCoordinateIntegral_arch_finite,
    sourceKPArchIntertwiner_product K hζ hs]

end
end ArtinMatthews
