module

public import ArtinMatthews.SourceAdelicHeightFibers
public import ArtinMatthews.SourceIntertwinerArchFinite
public import ArtinMatthews.SourceEisensteinOutgoingHeight
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

/-! The outgoing constant term has an exact height power on every fixed
finite fiber, retaining the original finite intertwining factor. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPArchMatrixHeight_pos (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    0 < sourceKPArchMatrixHeight K hζ g := by
  unfold sourceKPArchMatrixHeight
  exact Finset.prod_pos (fun v _ => pow_pos (sourceArchHeight_pos _) _)

include hζ in
theorem sourceKPFiniteMatrixHeightProduct_pos (g : GL (Fin 2) 𝔸ᶠ[K]) :
    0 < sourceKPFiniteMatrixHeightProduct K g := by
  have hp := sourceKPAdelicHeight_pos K hζ ((sourceKPGL2ProductEquiv K).symm (1,g))
  rw [sourceKPAdelicHeight_pair] at hp
  exact pos_of_mul_pos_right hp (sourceKPArchMatrixHeight_pos K hζ 1).le

theorem sourceKPAdelicTraceIntertwiner_norm_coverHeight {s : ℂ} (hs : 0 < s.re)
    (g : GL (Fin 2) (InfiniteAdeleRing K)) (qf : SourceKPFiniteAdeleProjective K hζ)
    (u : GL (Fin 2) 𝔸ᶠ[K])
    (hu : sourceKPFiniteAdeleProjectiveProjection K hζ qf = ProjGenLinGroup.mk u) :
    ‖sourceKPAdelicTraceIntertwiner K hζ s (ProjGenLinGroup.mk g,qf)‖ =
      (‖((Real.pi : ℂ) / s) ^ Fintype.card (InfinitePlace K) * sourceKPFiniteIntertwiner K hζ s qf‖ /
        sourceKPFiniteMatrixHeightProduct K u ^ (1 / 2 - s.re)) *
      sourceKPAdelicCoverHeight K hζ (ProjGenLinGroup.mk g,qf) ^ (1 / 2 - s.re) := by
  rw [sourceKPAdelicTraceIntertwiner_norm_height K hζ hs,
    sourceKPAdelicCoverHeight_arch_matrix K hζ qf u hu,
    Real.mul_rpow (sourceKPArchMatrixHeight_pos K hζ g).le (sourceKPFiniteMatrixHeightProduct_pos K hζ u).le]
  let A := ‖((Real.pi : ℂ) / s) ^ Fintype.card (InfinitePlace K) * sourceKPFiniteIntertwiner K hζ s qf‖
  let X := sourceKPArchMatrixHeight K hζ g ^ (1 / 2 - s.re)
  let Y := sourceKPFiniteMatrixHeightProduct K u ^ (1 / 2 - s.re)
  change A * X = (A / Y) * (X * Y)
  have hY : Y ≠ 0 := (Real.rpow_pos_of_pos (sourceKPFiniteMatrixHeightProduct_pos K hζ u) _).ne'
  calc
    A * X = (A * X * Y) / Y := (mul_div_cancel_right₀ _ hY).symm
    _ = _ := by ring

end
end ArtinMatthews
