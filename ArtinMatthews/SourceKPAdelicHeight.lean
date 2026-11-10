module

public import ArtinMatthews.SourceAdelicIwasawa
public import ArtinMatthews.SourceKPAdelicUnitTorus
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
public import Mathlib.NumberTheory.Height.NumberField
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

/-! The actual adelic Iwasawa height, with the normalized complex
place multiplicities and all finite factors retained. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicHeight (g : GL (Fin 2) 𝔸[K]) : ℝ :=
  sourceKPIdeleAbsoluteNorm K (GeneralLinearGroup.det (sourceKPAdelicIwasawaBorel K hζ g))

theorem sourceKPAdelicHeight_pos (g : GL (Fin 2) 𝔸[K]) : 0 < sourceKPAdelicHeight K hζ g :=
  sourceKPIdeleAbsoluteNorm_pos K _

theorem sourceKPAdelicFiniteCoordinate_det (g : GL (Fin 2) 𝔸[K])
    (P : HeightOneSpectrum (𝓞 K)) :
    sourceKPIdeleFiniteCoordinate K P (GeneralLinearGroup.det g) =
      GeneralLinearGroup.det (sourceKPAdelicBaseFiniteAt K P g) := by
  apply Units.ext
  change (Matrix.det (g : Matrix (Fin 2) (Fin 2) 𝔸[K])).2 P =
    Matrix.det (sourceKPAdelicBaseFiniteAt K P g : Matrix (Fin 2) (Fin 2) (P.adicCompletion K))
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  rfl

theorem sourceKPAdelicComplexCoordinate_det (g : GL (Fin 2) 𝔸[K]) (v : InfinitePlace K) :
    sourceKPArchComplexEquiv K hζ v
      (sourceKPIdeleInfiniteCoordinate K v (GeneralLinearGroup.det g) : v.Completion) =
        (GeneralLinearGroup.det (sourceKPAdelicBaseComplexAt K hζ v g) : ℂ) := by
  change sourceKPArchComplexEquiv K hζ v
    ((Matrix.det (g : Matrix (Fin 2) (Fin 2) 𝔸[K])).1 v) =
      Matrix.det (sourceKPAdelicBaseComplexAt K hζ v g : Matrix (Fin 2) (Fin 2) ℂ)
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  change sourceKPArchComplexEquiv K hζ v
    ((g 0 0).1 v * (g 1 1).1 v - (g 0 1).1 v * (g 1 0).1 v) =
    sourceKPArchComplexEquiv K hζ v ((g 0 0).1 v) *
        sourceKPArchComplexEquiv K hζ v ((g 1 1).1 v) -
      sourceKPArchComplexEquiv K hζ v ((g 0 1).1 v) *
        sourceKPArchComplexEquiv K hζ v ((g 1 0).1 v)
  rw [map_sub, map_mul, map_mul]

theorem sourceKPAdelicHeight_product (g : GL (Fin 2) 𝔸[K]) :
    sourceKPAdelicHeight K hζ g =
      (∏ v : InfinitePlace K, sourceArchHeight (sourceKPAdelicBaseComplexAt K hζ v g) ^ v.mult) *
        ∏ᶠ P : HeightOneSpectrum (𝓞 K),
          ‖(GeneralLinearGroup.det (sourceKPAdelicBaseFiniteAt K P g) : P.adicCompletion K)‖ /
            max ‖sourceKPAdelicBaseFiniteAt K P g 1 0‖ ‖sourceKPAdelicBaseFiniteAt K P g 1 1‖ ^ 2 := by
  change ‖(sourceKPIdeleInfiniteUnit K (GeneralLinearGroup.det
      (sourceKPAdelicIwasawaBorel K hζ g)) : InfiniteAdeleRing K)‖ *
    ‖(sourceKPIdeleFiniteUnit K (GeneralLinearGroup.det
      (sourceKPAdelicIwasawaBorel K hζ g)) : 𝔸ᶠ[K])‖ = _
  rw [InfiniteAdeleRing.norm_def, FiniteAdeleRing.norm_eq_finprod_of_unit]
  congr 1
  · apply Finset.prod_congr rfl
    intro v _
    change ‖(sourceKPIdeleInfiniteCoordinate K v (GeneralLinearGroup.det
      (sourceKPAdelicIwasawaBorel K hζ g)) : v.Completion)‖ ^ v.mult = _
    rw [← sourceKPArchComplexEquiv_norm K hζ v,
      sourceKPAdelicComplexCoordinate_det, sourceKPAdelicIwasawa_arch_torus_norm]
  · apply finprod_congr
    intro P
    change ‖(sourceKPIdeleFiniteCoordinate K P (GeneralLinearGroup.det
      (sourceKPAdelicIwasawaBorel K hζ g)) : P.adicCompletion K)‖ = _
    rw [sourceKPAdelicFiniteCoordinate_det, sourceKPAdelicIwasawa_finite_torus_norm]

end
end ArtinMatthews
