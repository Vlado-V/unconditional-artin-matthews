module

public import ArtinMatthews.SourceKPAdelicDefectRadialFormula
public import ArtinMatthews.SourceAdelicHeightFibers
public import ArtinMatthews.SourceKPAdelicBaseCompactTopology
public import ArtinMatthews.SourceKPAdelicHeightCompact
public import ArtinMatthews.SourceKPAdelicHeightFiniteBound
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

/-! The actual radial defect has locally finite rational support on
each full archimedean matrix fiber, uniformly in the spectral parameter. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Filter
open scoped NumberField AdeleRing MatrixGroups Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicDefectTerm_locally_finite {T : ℝ} (hT : 0 < T)
    (qf : SourceKPFiniteAdeleProjective K hζ) (g₀ : GL (Fin 2) (InfiniteAdeleRing K)) :
    ∃ I : Set (SourceKPRationalBorelCoset K), I.Finite ∧
      ∀ᶠ g : GL (Fin 2) (InfiniteAdeleRing K) in 𝓝 g₀, ∀ s c, c ∉ I →
        sourceKPAdelicDefectTerm K hζ T s (ProjGenLinGroup.mk g,qf) c = 0 := by
  obtain ⟨u,hu⟩ := ProjGenLinGroup.mk_surjective (sourceKPFiniteAdeleProjectiveProjection K hζ qf)
  let G : GL (Fin 2) (InfiniteAdeleRing K) → GL (Fin 2) 𝔸[K] :=
    fun g => (sourceKPGL2ProductEquiv K).symm (g,u)
  have hG : Continuous G := (sourceKPGL2ProductEquiv_symm_continuous K).comp
    (continuous_id.prodMk continuous_const)
  have hproj (g : GL (Fin 2) (InfiniteAdeleRing K)) :
      sourceKPAdelicProjectiveProjection K hζ (ProjGenLinGroup.mk g,qf) = ProjGenLinGroup.mk (G g) := by
    apply (sourceKPAdelicProjectiveProductEquiv K).injective
    rw [sourceKPAdelicProjectiveProjection_product,sourceKPAdelicProjectiveProductEquiv_mk]
    change (ProjGenLinGroup.mk g,sourceKPFiniteAdeleProjectiveProjection K hζ qf) =
      (ProjGenLinGroup.mk ((sourceKPGL2ProductEquiv K) (G g)).1,
       ProjGenLinGroup.mk ((sourceKPGL2ProductEquiv K) (G g)).2)
    simp only [G,MulEquiv.apply_symm_apply,hu]
  let B := sourceKPAdelicHeightConstant K hζ (G g₀)+1
  have hB : sourceKPAdelicHeightConstant K hζ (G g₀) < B := by dsimp [B]; linarith
  have hn : ∀ᶠ g in 𝓝 g₀, sourceKPAdelicHeightConstant K hζ (G g) < B :=
    ((sourceKPAdelicHeightConstant_continuous K hζ).comp hG).continuousAt (Iio_mem_nhds hB)
  obtain ⟨I,hI,hbound⟩ := sourceKPAdelicRationalHeight_finite_of_bound K hζ B (by linarith : 0 < T/2)
  refine ⟨I,hI,?_⟩
  filter_upwards [hn] with g hg
  intro s c hc
  have hle : sourceKPAdelicRationalHeight K hζ (ProjGenLinGroup.mk g,qf) c ≤ T/2 := by
    by_contra h
    exact hc (hbound (G g) hg.le _ (hproj g) c (lt_of_not_ge h))
  rw [sourceKPAdelicDefectTerm,sourceKPAdelicDefectCoefficient_zero hT hle,zero_mul]

end
end ArtinMatthews
