module

public import ArtinMatthews.SourceAdelicHeightFibers
public import ArtinMatthews.SourceIntertwinerArchFinite
public import ArtinMatthews.SourceArchIntertwinerProduct
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

/-! The outgoing constant term has its exact decreasing height power. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceArchSphericalProduct_norm_height (s : ℂ)
    (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    ‖sourceArchSphericalProduct K hζ s (ProjGenLinGroup.mk g)‖ =
      sourceKPArchMatrixHeight K hζ g ^ (s.re + 1 / 2) := by
  let := source_isTotallyComplex K hζ
  rw [sourceArchSphericalProduct_mk, norm_prod]
  unfold sourceKPArchMatrixHeight
  rw [← Real.finsetProd_rpow Finset.univ _ (fun v _ =>
    pow_nonneg (sourceArchHeight_pos _).le _) (s.re + 1 / 2)]
  apply Finset.prod_congr rfl
  intro v _
  let G := sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)
  have hG : 0 < sourceArchHeight G := sourceArchHeight_pos G
  change ‖sourceArchSphericalGL s G‖ = (sourceArchHeight G ^ v.mult) ^ (s.re + 1 / 2)
  rw [sourceArchSphericalGL, Complex.norm_cpow_eq_rpow_re_of_pos hG,
    NumberField.IsTotallyComplex.mult_eq, ← Real.rpow_two, ← Real.rpow_mul hG.le]
  congr 1
  norm_num [Complex.add_re, Complex.mul_re]
  ring

theorem sourceKPAdelicTraceIntertwiner_norm_height {s : ℂ} (hs : 0 < s.re)
    (g : GL (Fin 2) (InfiniteAdeleRing K)) (qf : SourceKPFiniteAdeleProjective K hζ) :
    ‖sourceKPAdelicTraceIntertwiner K hζ s (ProjGenLinGroup.mk g, qf)‖ =
      ‖((Real.pi : ℂ) / s) ^ Fintype.card (InfinitePlace K) * sourceKPFiniteIntertwiner K hζ s qf‖ *
        sourceKPArchMatrixHeight K hζ g ^ (1 / 2 - s.re) := by
  rw [sourceKPAdelicTraceIntertwiner_arch_formula K hζ hs, norm_mul, norm_mul,
    sourceArchSphericalProduct_norm_height, norm_mul]
  have he : (-s).re + 1 / 2 = 1 / 2 - s.re := by simp only [Complex.neg_re]; ring
  rw [he]
  ring

end
end ArtinMatthews
