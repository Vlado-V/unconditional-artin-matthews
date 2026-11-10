module

public import ArtinMatthews.SourceIntertwinerArchFinite
public import ArtinMatthews.SourceArchSphericalIntertwiner
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open NumberField IsDedekindDomain MeasureTheory SourceArchJacquet Matrix
open OAI.RepresentationTheory.Weil
open scoped NumberField AdeleRing MatrixGroups BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance archIntertwinerCompletionMeasurable (v : InfinitePlace K) : MeasurableSpace v.Completion := borel _
local instance archIntertwinerCompletionBorel (v : InfinitePlace K) : BorelSpace v.Completion := ⟨rfl⟩
local instance archIntertwinerInfiniteMeasurable : MeasurableSpace (InfiniteAdeleRing K) :=
  inferInstanceAs (MeasurableSpace (∀ v : InfinitePlace K, v.Completion))

theorem sourceKPAdelicWeyl_arch_component :
    (sourceKPAdelicProjectiveWeyl K hζ).1 =
      ProjGenLinGroup.mk (sourceKPWeylMatrix (InfiniteAdeleRing K)) := by
  change ProjGenLinGroup.map (algebraMap K (InfiniteAdeleRing K))
    (ProjGenLinGroup.mk (sourceKPWeylMatrix K)) = _
  rw [ProjGenLinGroup.map_mk, sourceKPWeylMatrix_map]

theorem sourceKPArchIntertwiningKernel_product (s : ℂ)
    (g : PGL(2, InfiniteAdeleRing K)) (x : InfiniteAdeleRing K) :
    sourceKPArchIntertwiningKernel K hζ s g x =
      ∏ v : InfinitePlace K, sourceArchSphericalSection s
        (sourcePGL2Weyl * sourcePGL2Upper (sourceKPArchComplexEquiv K hζ v (x v)) *
          sourceArchProjectiveAt K hζ v g) := by
  unfold sourceKPArchIntertwiningKernel sourceArchSphericalProduct
  apply Finset.prod_congr rfl
  intro v _
  rw [map_mul, map_mul, sourceKPAdelicWeyl_arch_component]
  have hw : sourceArchProjectiveAt K hζ v
      (ProjGenLinGroup.mk (sourceKPWeylMatrix (InfiniteAdeleRing K))) = sourcePGL2Weyl := by
    rw [sourceArchProjectiveAt, ProjGenLinGroup.map_mk,
      sourceKPWeylMatrix_map, sourceKPWeylMatrix_field]
  have hn : sourceArchProjectiveAt K hζ v
      (ProjGenLinGroup.mk (sourceKPUpperMatrix (InfiniteAdeleRing K) x)) =
      sourcePGL2Upper (sourceKPArchComplexEquiv K hζ v (x v)) := by
    rw [sourceArchProjectiveAt, ProjGenLinGroup.map_mk, sourceKPUpperMatrix_map,
      sourceKPUpperMatrix_field]
    rfl
  rw [hw, hn]

theorem sourceKPArchIntertwiner_product {s : ℂ} (hs : 0 < s.re)
    (g : PGL(2, InfiniteAdeleRing K)) :
    sourceKPArchIntertwiner K hζ s g =
      ((Real.pi : ℂ) / s) ^ Fintype.card (InfinitePlace K) *
        sourceArchSphericalProduct K hζ (-s) g := by
  let := source_isTotallyComplex K hζ
  let μ (v : InfinitePlace K) :=
    Local.FunctionsMetaplectic.Construction.selfDualMeasure v.Completion
      (StandardAdelic.localInfiniteCharacter K v)
  have hc (v : InfinitePlace K) : InfinitePlace.IsComplex v :=
    IsTotallyComplex.isComplex v
  let (v : InfinitePlace K) : SigmaFinite (μ v) := by
    have hm : (μ v).map (sourceArchCompletionEquiv K v (hc v)) =
        VaryingKummerAnalytic.sourceComplexTraceMeasure :=
      sourceArchCompletion_selfDualMeasure K v (hc v)
    have hmfinite : SigmaFinite ((μ v).map (sourceArchCompletionEquiv K v (hc v))) := by
      rw [hm]
      change SigmaFinite ((2 : NNReal) • (volume : Measure ℂ))
      infer_instance
    exact SigmaFinite.of_map (μ v)
      (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex
        (hc v)).continuous.measurable.aemeasurable
      hmfinite
  unfold sourceKPArchIntertwiner
  simp_rw [sourceKPArchIntertwiningKernel_product]
  change (∫ x : (v : InfinitePlace K) → v.Completion,
    ∏ v, sourceArchSphericalSection s
      (sourcePGL2Weyl * sourcePGL2Upper (sourceKPArchComplexEquiv K hζ v (x v)) *
        sourceArchProjectiveAt K hζ v g) ∂Measure.pi μ) = _
  rw [integral_fintype_prod_eq_prod (μ := μ)
    (fun (v : InfinitePlace K) (x : v.Completion) =>
      sourceArchSphericalSection s
        (sourcePGL2Weyl * sourcePGL2Upper (sourceKPArchComplexEquiv K hζ v x) *
          sourceArchProjectiveAt K hζ v g))]
  have hlocal (v : InfinitePlace K) :
      (∫ x : v.Completion, sourceArchSphericalSection s
        (sourcePGL2Weyl * sourcePGL2Upper (sourceKPArchComplexEquiv K hζ v x) *
          sourceArchProjectiveAt K hζ v g) ∂μ v) =
        ((Real.pi : ℂ) / s) * sourceArchSphericalSection (-s)
          (sourceArchProjectiveAt K hζ v g) := by
    have h := sourceArchCompletion_integral K v (hc v) (fun z =>
      sourceArchSphericalSection s
        (sourcePGL2Weyl * sourcePGL2Upper z * sourceArchProjectiveAt K hζ v g))
    change (∫ x : v.Completion, sourceArchSphericalSection s
      (sourcePGL2Weyl * sourcePGL2Upper (sourceKPArchComplexEquiv K hζ v x) *
        sourceArchProjectiveAt K hζ v g) ∂μ v) =
        sourceArchSphericalIntertwiner s (sourceArchProjectiveAt K hζ v g) at h
    rw [h, sourceArchSphericalIntertwiner_eq hs]
  simp_rw [hlocal]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ]
  rfl

theorem sourceKPAdelicTraceIntertwiner_arch_formula {s : ℂ} (hs : 0 < s.re)
    (g : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicTraceIntertwiner K hζ s g =
      ((Real.pi : ℂ) / s) ^ Fintype.card (InfinitePlace K) *
        sourceArchSphericalProduct K hζ (-s) g.1 *
        sourceKPFiniteIntertwiner K hζ s g.2 := by
  rw [sourceKPAdelicTraceIntertwiner_arch_finite,
    sourceKPArchIntertwiner_product K hζ hs]

theorem sourceKPAdelicTraceIntertwiner_at_finite {s : ℂ} (hs : 0 < s.re)
    (g : SourceKPFiniteAdeleProjective K hζ) :
    sourceKPAdelicTraceIntertwiner K hζ s (1, g) =
      ((Real.pi : ℂ) / s) ^ Fintype.card (InfinitePlace K) *
        sourceKPFiniteIntertwiner K hζ s g := by
  rw [sourceKPAdelicTraceIntertwiner_arch_formula K hζ hs]
  simp only [sourceArchSphericalProduct, map_one, sourceArchSphericalSection_one,
    Finset.prod_const_one, mul_one]

end
end ArtinMatthews
