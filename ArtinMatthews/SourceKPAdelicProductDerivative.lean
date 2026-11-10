module

public import ArtinMatthews.SourceKPAdelicRationalProductChart
public import ArtinMatthews.SourceKPArchProductDerivative
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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

/-! Actual global spherical and rational-summand derivative bounds,
with the arbitrary finite scalar retained. -/

namespace ArtinMatthews
open NumberField Matrix OAI.CubicEisenstein SourceArchJacquet Filter
open scoped NumberField MatrixGroups AdeleRing Topology BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicProductSection_fderiv_bound (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (p : InfinitePlace K → EuclideanSpatial)
    (hp : ∀ v, 0 < p v 2) :
    ‖fderiv ℝ (sourceKPAdelicProductSection K hζ s q) p‖ ≤
      (∑ v, 3*‖2*s+1‖/(p v 2))*‖sourceKPAdelicProductSection K hζ s q p‖ := by
  rcases q with ⟨a,qf⟩
  obtain ⟨g,rfl⟩ := ProjGenLinGroup.mk_surjective a
  let A := fun v => sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)
  let C := sourceKPAdelicCompactScalar K hζ s (1,qf)
  have he : sourceKPAdelicProductSection K hζ s (ProjGenLinGroup.mk g,qf) =ᶠ[𝓝 p]
      fun x => C*sourceArchTranslatedCoordinateProduct s A x := by
    filter_upwards [sourceKPAdelicProductSection_eventually_factor K hζ s g qf p hp] with x hx
    exact hx.trans (mul_comm _ _)
  have hd := ((sourceArchTranslatedCoordinateProduct_contDiffAt s A p hp).differentiableAt
    (by simp)).hasFDerivAt.const_smul C
  have hderiv : fderiv ℝ (fun x => C*sourceArchTranslatedCoordinateProduct s A x) p =
      C • fderiv ℝ (sourceArchTranslatedCoordinateProduct s A) p := hd.fderiv
  rw [he.fderiv_eq,hderiv,norm_smul]
  calc
    ‖C‖*‖fderiv ℝ (sourceArchTranslatedCoordinateProduct s A) p‖ ≤
        ‖C‖*((∑ v, 3*‖2*s+1‖/(p v 2))*‖sourceArchTranslatedCoordinateProduct s A p‖) :=
      mul_le_mul_of_nonneg_left (sourceArchTranslatedCoordinateProduct_fderiv_bound s A p hp)
        (norm_nonneg _)
    _ = (∑ v, 3*‖2*s+1‖/(p v 2))*
        ‖sourceKPAdelicProductSection K hζ s (ProjGenLinGroup.mk g,qf) p‖ := by
      rw [he.eq_of_nhds,norm_mul]
      ring

theorem sourceKPAdelicRationalProductChart_fderiv_bound (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (c : SourceKPRationalBorelCoset K)
    (p : InfinitePlace K → EuclideanSpatial) (hp : ∀ v, 0 < p v 2) :
    ‖fderiv ℝ (sourceKPAdelicRationalProductChart K hζ s q c) p‖ ≤
      (∑ v, 3*‖2*s+1‖/(p v 2))*‖sourceKPAdelicRationalProductChart K hζ s q c p‖ := by
  induction c using Quotient.inductionOn with
  | _ γ =>
    have h := sourceKPAdelicProductSection_fderiv_bound K hζ s
      (sourceKPAdelicProjectiveRationalLift K hζ γ*q) p hp
    rw [← sourceKPAdelicRationalProductChart_mk] at h
    exact h

end
end ArtinMatthews
