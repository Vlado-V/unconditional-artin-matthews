module

public import ArtinMatthews.SourceProductSmoothExhaustion
public import ArtinMatthews.SourceKPAdelicHeightProductChart
public import ArtinMatthews.SourceKPArchActionSmooth
public import ArtinMatthews.SourceEisensteinOutgoingCoverHeight
public import ArtinMatthews.SourceKPArchProjectiveEnergy
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
open NumberField Matrix OAI.CubicEisenstein SourceArchJacquet SourceHyperbolicGreen Filter
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPArchEuclideanAction_height
    (g : GL (Fin 2) (InfiniteAdeleRing K))
    (p : ProductSpace (InfinitePlace K)) (hp : p ∈ productUpper (InfinitePlace K))
    (v : InfinitePlace K) :
    sourceKPArchEuclideanAction K hζ (ProjGenLinGroup.mk g) p v 2 =
      sourceArchHeight
        (sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v) *
          (upperSection ((p v 0 : ℂ) + (p v 1 : ℂ) * Complex.I) (p v 2)
            (productUpper_pos hp v) : GL (Fin 2) ℂ)) := by
  rw [sourceKPArchEuclideanAction_apply, sourceKPArchProjectiveAt_mk]
  unfold sourceArchEuclideanProjectiveAction
  rw [sourceArchProjectiveUpperAction_mk,
    sourceArchEuclideanUpperMap_positive _ (productUpper_pos hp v)]
  change sourceArchHeight
      (sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v) *
        (upperSection ((p v 0 : ℂ) + Complex.I * (p v 1 : ℂ)) (p v 2)
          (productUpper_pos hp v) : GL (Fin 2) ℂ)) = _
  have hz : (p v 0 : ℂ) + Complex.I * (p v 1 : ℂ) =
      (p v 0 : ℂ) + (p v 1 : ℂ) * Complex.I := by ring
  rw [hz]

theorem sourceKPAdelicProductHeight_action
    (g : GL (Fin 2) (InfiniteAdeleRing K)) (qf : SourceKPFiniteAdeleProjective K hζ)
    (u : GL (Fin 2) 𝔸ᶠ[K])
    (hu : sourceKPFiniteAdeleProjectiveProjection K hζ qf = ProjGenLinGroup.mk u)
    (p : ProductSpace (InfinitePlace K)) (hp : p ∈ productUpper (InfinitePlace K)) :
    sourceKPAdelicProductHeight K hζ (ProjGenLinGroup.mk g, qf) p =
      sourceKPFiniteMatrixHeightProduct K u *
        ∏ v, (sourceKPArchEuclideanAction K hζ (ProjGenLinGroup.mk g) p v 2) ^ 2 := by
  have := source_isTotallyComplex K hζ
  rw [sourceKPAdelicProductHeight_factor K hζ g qf u hu p (fun v => productUpper_pos hp v),
    mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  rw [NumberField.IsTotallyComplex.mult_eq, sourceKPArchEuclideanAction_height K hζ g p hp v]
  congr 1
  simp only [sourceArchTranslatedSectionChart, dite_eq_left (productUpper_pos hp v),
    sourceArchSphericalGL, mul_zero, zero_add, Complex.cpow_one, Complex.ofReal_re]

def sourceKPProductHeightExhaustion (q : SourceKPAdelicProjective K hζ)
    (a : ℝ) (p : ProductSpace (InfinitePlace K)) : ℝ :=
  1 - Real.smoothTransition (Real.log (sourceKPAdelicProductHeight K hζ q p) - a)

theorem sourceKPProductHeightExhaustion_eventuallyEq
    (g : GL (Fin 2) (InfiniteAdeleRing K)) (qf : SourceKPFiniteAdeleProjective K hζ)
    (u : GL (Fin 2) 𝔸ᶠ[K])
    (hu : sourceKPFiniteAdeleProjectiveProjection K hζ qf = ProjGenLinGroup.mk u)
    (a : ℝ) (p : ProductSpace (InfinitePlace K))
    (hp : p ∈ productUpper (InfinitePlace K)) :
    sourceKPProductHeightExhaustion K hζ (ProjGenLinGroup.mk g, qf) a =ᶠ[𝓝 p]
      fun x => sourceProductSmoothExhaustion (sourceKPFiniteMatrixHeightProduct K u) a
        (sourceKPArchEuclideanAction K hζ (ProjGenLinGroup.mk g) x) := by
  filter_upwards [sourceKPProductUpper_eventually K p (fun v => productUpper_pos hp v)] with x hx
  have hxu : x ∈ productUpper (InfinitePlace K) := fun v _ => hx v
  unfold sourceKPProductHeightExhaustion sourceProductSmoothExhaustion
  rw [sourceKPAdelicProductHeight_action K hζ g qf u hu x hxu,
    sourceProductLogHeight_eq _ (sourceKPFiniteMatrixHeightProduct_pos K hζ u) _
      (sourceKPArchEuclideanAction_positive K hζ _ x)]

theorem sourceKPProductHeightExhaustion_energy_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (q : SourceKPAdelicProjective K hζ) (a : ℝ)
      (p : ProductSpace (InfinitePlace K)), p ∈ productUpper (InfinitePlace K) →
      productGradientEnergy (fun x => (sourceKPProductHeightExhaustion K hζ q a x : ℂ)) p ≤
        4 * Fintype.card (InfinitePlace K) * B ^ 2 := by
  obtain ⟨B,hB,hbound⟩ := sourceProductSmoothExhaustion_energy_bound (ι := InfinitePlace K)
  refine ⟨B,hB,?_⟩
  rintro ⟨qI,qf⟩ a p hp
  obtain ⟨g,rfl⟩ := ProjGenLinGroup.mk_surjective qI
  obtain ⟨u,hu⟩ := ProjGenLinGroup.mk_surjective
    (sourceKPFiniteAdeleProjectiveProjection K hζ qf)
  let F : ProductSpace (InfinitePlace K) → ℂ :=
    fun x => (sourceProductSmoothExhaustion (sourceKPFiniteMatrixHeightProduct K u) a x : ℂ)
  have he : (fun x => (sourceKPProductHeightExhaustion K hζ (ProjGenLinGroup.mk g,qf) a x : ℂ))
      =ᶠ[𝓝 p] F ∘ sourceKPArchEuclideanAction K hζ (ProjGenLinGroup.mk g) := by
    filter_upwards [sourceKPProductHeightExhaustion_eventuallyEq K hζ g qf u hu.symm a p hp]
      with x hx
    exact congrArg Complex.ofReal hx
  have hf : DifferentiableAt ℝ F
      (sourceKPArchEuclideanAction K hζ (ProjGenLinGroup.mk g) p) :=
    (Complex.ofRealCLM.differentiableAt.comp _
      ((sourceProductSmoothExhaustion_contDiffAt _ a _
        (sourceKPArchEuclideanAction_positive K hζ _ p)).differentiableAt (by norm_num)))
  have heE : productGradientEnergy
      (fun x => (sourceKPProductHeightExhaustion K hζ (ProjGenLinGroup.mk g,qf) a x : ℂ)) p =
      productGradientEnergy (F ∘ sourceKPArchEuclideanAction K hζ (ProjGenLinGroup.mk g)) p := by
    simp only [productGradientEnergy, productPartial, he.fderiv_eq (𝕜 := ℝ)]
  rw [heE, sourceKPArchEuclideanAction_gradientEnergy K hζ _ F p hp hf]
  exact hbound _ a _ (sourceKPArchEuclideanAction_positive K hζ _ p)

end
end ArtinMatthews
