module

public import ArtinMatthews.SourceKPTraceJacquetArchFinite
public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.MeasureTheory.Integral.Pi


set_option backward.privateInPublic true
@[expose] public section

/-! The archimedean factor is the finite product of actual local
trace Jacquet integrals. Each integral uses its local self-dual
measure and is absolutely convergent in the right half-plane. -/

namespace ArtinMatthews
open NumberField MeasureTheory Matrix StandardAdelic SourceArchJacquet
open OAI.RepresentationTheory.Weil OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField AdeleRing MatrixGroups Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance sourceKPTraceJacquetArchCompletionMeasurable (v : InfinitePlace K) :
    MeasurableSpace v.Completion := borel v.Completion
local instance sourceKPTraceJacquetArchCompletionBorel (v : InfinitePlace K) :
    BorelSpace v.Completion := ⟨rfl⟩
local instance sourceKPTraceJacquetArchInfiniteMeasurable : MeasurableSpace (InfiniteAdeleRing K) :=
  inferInstanceAs (MeasurableSpace (∀ v : InfinitePlace K, v.Completion))

theorem sourceKPTraceJacquetArchCharacter_product (m : Kˣ) (x : InfiniteAdeleRing K) :
    sourceKPTraceJacquetArchCharacter K m x =
      ∏ v : InfinitePlace K, star (localInfiniteCharacter K v (algebraMap K v.Completion (m : K) * x v)) := by
  let a : ∀ v : InfinitePlace K, v.Completion :=
    fun v => algebraMap K v.Completion (m : K) * x v
  let b (v : InfinitePlace K) : ∀ w : InfinitePlace K, w.Completion := Pi.single v (a v)
  let ψ : (∀ v : InfinitePlace K, v.Completion) → ℂ := fun z => archCharacter K z
  have hzero : ψ 0 = 1 := AddChar.map_zero_eq_one (archCharacter K)
  have hadd (u z : ∀ v : InfinitePlace K, v.Completion) : ψ (u+z) = ψ u * ψ z :=
    AddChar.map_add_eq_mul (archCharacter K) u z
  have hsingle (v : InfinitePlace K) : ψ (b v) = localInfiniteCharacter K v (a v) :=
    (localInfiniteCharacter_single K v (a v)).symm
  have hsum : (∑ v : InfinitePlace K, b v) = a := by
    funext v
    simp only [Finset.sum_apply]
    exact Fintype.sum_pi_single v a
  have hp (T : Finset (InfinitePlace K)) :
      ψ (∑ v ∈ T, b v) = ∏ v ∈ T, localInfiniteCharacter K v (a v) := by
    induction T using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.prod_empty, hzero]
    | insert v T hv ih =>
      rw [Finset.sum_insert hv, Finset.prod_insert hv, hadd, ih, hsingle]
  have he := (congrArg ψ hsum).symm.trans (hp Finset.univ)
  change star (ψ a) = ∏ v : InfinitePlace K, star (localInfiniteCharacter K v (a v))
  rw [he, star_prod]

def sourceKPTraceJacquetLocalArchKernel (m : Kˣ) (s : ℂ)
    (g : PGL(2, InfiniteAdeleRing K)) (v : InfinitePlace K) (x : v.Completion) : ℂ :=
  star (localInfiniteCharacter K v (algebraMap K v.Completion (m : K) * x)) *
    sourceArchSphericalSection s
      (sourcePGL2Weyl * sourcePGL2Upper (sourceKPArchComplexEquiv K hζ v x) *
        sourceArchProjectiveAt K hζ v g)

theorem sourceKPTraceJacquetArchKernel_product (m : Kˣ) (s : ℂ)
    (g : PGL(2, InfiniteAdeleRing K)) (x : InfiniteAdeleRing K) :
    sourceKPTraceJacquetArchKernel K hζ m s g x =
      ∏ v : InfinitePlace K, sourceKPTraceJacquetLocalArchKernel K hζ m s g v (x v) := by
  unfold sourceKPTraceJacquetArchKernel sourceKPTraceJacquetLocalArchKernel
  rw [sourceKPTraceJacquetArchCharacter_product, sourceKPArchIntertwiningKernel_product,
    Finset.prod_mul_distrib]

theorem sourceKPTraceJacquetLocalArchKernel_integrable {s : ℂ} (hs : 0 < s.re)
    (m : Kˣ) (g : PGL(2, InfiniteAdeleRing K)) (v : InfinitePlace K) :
    Integrable (sourceKPTraceJacquetLocalArchKernel K hζ m s g v)
      (Local.FunctionsMetaplectic.Construction.selfDualMeasure v.Completion
        (localInfiniteCharacter K v)) := by
  let := source_isTotallyComplex K hζ
  let hc : InfinitePlace.IsComplex v := IsTotallyComplex.isComplex v
  let gC := sourceArchProjectiveAt K hζ v g
  let f : ℂ → ℂ := fun x => sourceArchSphericalSection s (sourcePGL2Weyl * sourcePGL2Upper x * gC)
  have hf := sourceArchCompletion_integrable K v hc f
    (sourceArchSphericalIntertwiner_integrable hs gC)
  have hχ : Continuous (localInfiniteCharacter K v) :=
    Characters.Construction.localAdditiveCharacter_continuous K (character K) (character_continuous K) (.inl v)
  have hw : Continuous (fun x : v.Completion =>
      star (localInfiniteCharacter K v (algebraMap K v.Completion (m : K) * x))) :=
    continuous_star.comp (hχ.comp (continuous_const.mul continuous_id))
  refine hf.bdd_mul (c := 1) hw.aestronglyMeasurable ?_
  filter_upwards with x
  rw [norm_star, localInfiniteCharacter_single]
  exact (archCharacter_unitary K (Pi.single v (algebraMap K v.Completion (m : K) * x))).le

theorem sourceKPTraceJacquetArchKernel_integral_product {s : ℂ} (hs : 0 < s.re)
    (m : Kˣ) (g : PGL(2, InfiniteAdeleRing K)) :
    Integrable (sourceKPTraceJacquetArchKernel K hζ m s g) (sourceKPArchSelfDualProduct K) ∧
    (∫ x, sourceKPTraceJacquetArchKernel K hζ m s g x ∂sourceKPArchSelfDualProduct K) =
      ∏ v : InfinitePlace K, ∫ x : v.Completion, sourceKPTraceJacquetLocalArchKernel K hζ m s g v x
        ∂Local.FunctionsMetaplectic.Construction.selfDualMeasure v.Completion (localInfiniteCharacter K v) := by
  let := source_isTotallyComplex K hζ
  let μ (v : InfinitePlace K) := Local.FunctionsMetaplectic.Construction.selfDualMeasure v.Completion
    (localInfiniteCharacter K v)
  let (v : InfinitePlace K) : SigmaFinite (μ v) := by
    let hv : InfinitePlace.IsComplex v := IsTotallyComplex.isComplex v
    have hm : (μ v).map (sourceArchCompletionEquiv K v hv) =
        VaryingKummerAnalytic.sourceComplexTraceMeasure := sourceArchCompletion_selfDualMeasure K v hv
    have hσ : SigmaFinite ((μ v).map (sourceArchCompletionEquiv K v hv)) := by
      rw [hm]
      change SigmaFinite ((2 : NNReal) • (volume : Measure ℂ))
      infer_instance
    exact SigmaFinite.of_map (μ v)
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).continuous.measurable.aemeasurable hσ
  let f := sourceKPTraceJacquetLocalArchKernel K hζ m s g
  have he : sourceKPTraceJacquetArchKernel K hζ m s g =
      fun x => ∏ v : InfinitePlace K, f v (x v) :=
    funext (sourceKPTraceJacquetArchKernel_product K hζ m s g)
  rw [he]
  change Integrable (fun (x : ∀ v : InfinitePlace K, v.Completion) => ∏ v, f v (x v)) (Measure.pi μ) ∧
    (∫ x : ∀ v : InfinitePlace K, v.Completion, ∏ v, f v (x v) ∂Measure.pi μ) =
      ∏ v : InfinitePlace K, ∫ x : v.Completion, f v x ∂μ v
  exact ⟨Integrable.fintype_prod_dep (fun v => sourceKPTraceJacquetLocalArchKernel_integrable K hζ hs m g v),
    integral_fintype_prod_eq_prod f⟩

end
end ArtinMatthews
