module

public import ArtinMatthews.SourceKPRadialHighFlow
public import ArtinMatthews.SourceArchOnlyIdele
public import ArtinMatthews.SourceArchRadialSectionDiagonal
public import ArtinMatthews.SourceKPAdelicCompactIntersection
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

/-! The actual balanced radial flow is right multiplication by the genuine
all-place expanding diagonal on the upper section. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPBalancedArchUnit (t : ℝ) : (InfiniteAdeleRing K)ˣ :=
  MulEquiv.piUnits.symm fun v => Units.map (sourceKPArchComplexEquiv K hζ v).symm
    (Units.mk0 (Real.exp t : ℂ) (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t)))

theorem sourceKPBalancedArchUnit_at (t : ℝ) (v : InfinitePlace K) :
    Units.map (sourceKPArchComplexEquiv K hζ v) (MulEquiv.piUnits (sourceKPBalancedArchUnit K hζ t) v) =
      Units.mk0 (Real.exp t : ℂ) (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t)) := by
  dsimp only [sourceKPBalancedArchUnit]
  rw [MulEquiv.apply_symm_apply]
  apply Units.ext
  exact (sourceKPArchComplexEquiv K hζ v).apply_symm_apply _

theorem sourceKPBalancedArchUnit_norm_at (t : ℝ) (v : InfinitePlace K) :
    ‖(sourceKPBalancedArchUnit K hζ t : InfiniteAdeleRing K) v‖ = Real.exp t := by
  have he : sourceKPArchComplexEquiv K hζ v ((sourceKPBalancedArchUnit K hζ t : InfiniteAdeleRing K) v) =
      (Real.exp t : ℂ) := congrArg Units.val (sourceKPBalancedArchUnit_at K hζ t v)
  rw [← sourceKPArchComplexEquiv_norm K hζ v,he,Complex.norm_real,Real.norm_of_nonneg (Real.exp_nonneg t)]

theorem sourceKPBalancedArchUnit_norm (t : ℝ) :
    ‖(sourceKPBalancedArchUnit K hζ t : InfiniteAdeleRing K)‖ = sourceKPRadialHeightScale K t := by
  let := source_isTotallyComplex K hζ
  rw [InfiniteAdeleRing.norm_def]
  simp_rw [sourceKPBalancedArchUnit_norm_at,NumberField.IsTotallyComplex.mult_eq]
  rw [sourceKPRadialHeightScale,Finset.prod_const,Finset.card_univ,← Real.exp_nat_mul,← Real.exp_nat_mul]
  congr 1
  ring

theorem sourceKPArchOnlyDiagonal_product (a : (InfiniteAdeleRing K)ˣ) :
    sourceKPGL2ProductEquiv K (sourceKPDiagonalHom 𝔸[K] (sourceArchOnlyIdele K a)) =
      (sourceKPDiagonalHom (InfiniteAdeleRing K) a,1) := by
  apply Prod.ext
  · apply GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · apply GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl

theorem sourceKPArchRadialFlowMatrix_section_diagonal (t : ℝ) (p : SourceKPArchUpperHalfSpace K) :
    sourceKPArchRadialFlowMatrix K hζ t (sourceKPArchUpperHalfSection K hζ p) =
      sourceKPArchUpperHalfSection K hζ p *
        sourceKPDiagonalHom (InfiniteAdeleRing K) (sourceKPBalancedArchUnit K hζ t) := by
  apply (sourceArchGLPiEquiv K).injective
  funext v
  apply (sourceKPArchMatrixComplexEquiv K hζ v).injective
  simp only [sourceKPArchRadialFlowMatrix_at,map_mul,Pi.mul_apply,sourceKPArchUpperHalfSection_at]
  rw [sourceArchRadialFlow_section_diagonal]
  congr 1
  rw [sourceArchPositiveDiagonal,← sourceKPBalancedArchUnit_at K hζ t v]
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · rfl
  · change 0 = sourceKPArchComplexEquiv K hζ v (0 : v.Completion)
    exact (map_zero _).symm
  · change 0 = sourceKPArchComplexEquiv K hζ v (0 : v.Completion)
    exact (map_zero _).symm
  · change 1 = sourceKPArchComplexEquiv K hζ v (1 : v.Completion)
    exact (map_one _).symm

end
end ArtinMatthews
