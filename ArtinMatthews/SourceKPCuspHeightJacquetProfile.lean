module

public import ArtinMatthews.SourceKPCuspNativeUpperPoint
public import ArtinMatthews.SourceKPArchJacquetProfile


set_option backward.privateInPublic true
@[expose] public section

/-! The fixed-finite height section has exactly the normalized product
archimedean Fourier factor, for arbitrary rational frequency. -/
namespace ArtinMatthews
open NumberField MeasureTheory StandardAdelic Matrix SourceArchJacquet
open OAI.RepresentationTheory.Weil
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance sourceHeightProfileCompletionMeasurable (v : InfinitePlace K) : MeasurableSpace v.Completion := borel _
local instance sourceHeightProfileCompletionBorel (v : InfinitePlace K) : BorelSpace v.Completion := ⟨rfl⟩
local instance sourceHeightProfileInfiniteMeasurable : MeasurableSpace (InfiniteAdeleRing K) :=
  inferInstanceAs (MeasurableSpace (∀ v : InfinitePlace K, v.Completion))

theorem sourceKPCuspHeightSection_at (y : InfinitePlace K → ℝ) (hy : ∀ v, 0 < y v)
    (v : InfinitePlace K) :
    sourceArchProjectiveAt K hζ v (sourceKPCuspHeightSection K hζ y hy) =
      sourcePGL2Diagonal (Units.mk0 (y v:ℂ) (Complex.ofReal_ne_zero.mpr (hy v).ne')) := by
  rw [sourceKPCuspHeightSection,sourceArchProjectiveAt_mk]
  simp only [sourceArchUpperHalfspaceMatrix,MulEquiv.apply_symm_apply]
  change sourceArchUpperPoint ((0:ℂ)+(0:ℂ)*Complex.I) (y v) (hy v) = _
  rw [zero_mul,zero_add,sourceArchUpperPoint_normalized,sourceKPUpperMatrix_zero,map_one,
    one_mul,sourceKPDiagonalHom_field]

theorem sourceKPCuspHeightSection_local_jacquet (m : Kˣ) (s : ℂ)
    (y : InfinitePlace K → ℝ) (hy : ∀ v, 0 < y v) (v : InfinitePlace K) :
    (∫ x, sourceKPTraceJacquetLocalArchKernel K hζ m s (sourceKPCuspHeightSection K hζ y hy) v x
      ∂Local.FunctionsMetaplectic.Construction.selfDualMeasure v.Completion (localInfiniteCharacter K v)) =
      sourceArchWeightedDiagonalProfile sourceArchTraceCharacter s
        (sourceKPTraceJacquetProfileFrequency K hζ m v) (y v) := by
  let hv : InfinitePlace.IsComplex v := (source_isTotallyComplex K hζ).isComplex v
  let e := sourceArchCompletionEquiv K v hv
  let a := sourceKPTraceJacquetProfileFrequency K hζ m v
  let u : ℂˣ := Units.mk0 (y v:ℂ) (Complex.ofReal_ne_zero.mpr (hy v).ne')
  let F : ℂ → ℂ := fun z => sourceArchTraceCharacter (a*z) *
    sourceArchSphericalSection s (sourcePGL2Weyl*sourcePGL2Upper z*sourcePGL2Diagonal u)
  have he : (fun x => sourceKPTraceJacquetLocalArchKernel K hζ m s (sourceKPCuspHeightSection K hζ y hy) v x) =
      fun x => F (e x) := by
    funext x
    rw [sourceKPTraceJacquetLocalArchKernel,sourceKPLocalInfiniteCharacter_star,
      sourceArchCompletion_character K v hv,sourceKPCuspHeightSection_at]
    simp only [map_neg,map_mul]
    dsimp only [F,a,e,u,sourceKPTraceJacquetProfileFrequency]
    simp only [neg_mul] <;> rfl
  rw [he,sourceArchCompletion_integral K v hv F,
    ← sourceArchWeightedDiagonalProfile_eq_integral sourceArchTraceCharacter s a u]
  have hn : ‖(u:ℂ)‖ = y v := by
    change ‖(y v:ℂ)‖ = y v
    rw [Complex.norm_real,Real.norm_of_nonneg (hy v).le]
  rw [hn]

theorem sourceKPCuspHeightSection_arch_jacquet {s : ℂ} (hs : 0 < s.re) (m : Kˣ)
    (y : InfinitePlace K → ℝ) (hy : ∀ v, 0 < y v) :
    (∫ x, sourceKPTraceJacquetArchKernel K hζ m s (sourceKPCuspHeightSection K hζ y hy) x
      ∂sourceKPArchSelfDualProduct K) = sourceKPTraceJacquetArchProfile K hζ m s y := by
  rw [(sourceKPTraceJacquetArchKernel_integral_product K hζ hs m _).2]
  apply Finset.prod_congr rfl
  intro v _
  exact sourceKPCuspHeightSection_local_jacquet K hζ m s y hy v

end
end ArtinMatthews
