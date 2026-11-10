module

public import ArtinMatthews.SourceArchOnlyIdele
public import ArtinMatthews.SourceArchIwasawaCompletion
public import ArtinMatthews.SourceKPIdeleComplexNorm
public import ArtinMatthews.SourceKPAdelicCompactIntersection
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Ring.IsFormallyReal
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

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open SourceArchJacquet
open scoped NumberField AdeleRing MatrixGroups BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K]

omit [NumberField K] in
theorem sourceArchUnit_value_ne_zero (a : (InfiniteAdeleRing K)ˣ) (v : InfinitePlace K) :
    (a : InfiniteAdeleRing K) v ≠ 0 := by
  intro hv
  have he := congrArg (fun x : InfiniteAdeleRing K => x v) a.val_inv
  change (a : InfiniteAdeleRing K) v * ((a⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) v = 1 at he
  rw [hv, zero_mul] at he
  exact zero_ne_one he

theorem sourceArchOnlyIdele_character_product (s : ℂ) (a : (InfiniteAdeleRing K)ˣ) :
    (sourceKPIdeleComplexNorm K s (sourceArchOnlyIdele K a) : ℂ) =
      ∏ v : InfinitePlace K, (‖(a : InfiniteAdeleRing K) v‖ : ℂ)^((v.mult : ℂ)*s) := by
  have hn (v : InfinitePlace K) : 0 < ‖(a : InfiniteAdeleRing K) v‖ :=
    norm_pos_iff.mpr (sourceArchUnit_value_ne_zero K a v)
  rw [sourceKPIdeleComplexNorm_coe, sourceArchOnlyIdele_norm, InfiniteAdeleRing.norm_def,
    Real.log_prod (fun v _ => pow_ne_zero _ (hn v).ne')]
  push_cast
  rw [Finset.mul_sum, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro v _
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (hn v).ne'),
    ← Complex.ofReal_log (hn v).le, Real.log_pow]
  push_cast
  congr 1
  ring

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceArchOnlyIdele_character_complex (s : ℂ) (a : (InfiniteAdeleRing K)ˣ) :
    (sourceKPIdeleComplexNorm K s (sourceArchOnlyIdele K a) : ℂ) =
      ∏ v : InfinitePlace K,
        (‖sourceKPArchComplexEquiv K hζ v ((a : InfiniteAdeleRing K) v)‖ : ℂ)^(2*s) := by
  have := source_isTotallyComplex K hζ
  rw [sourceArchOnlyIdele_character_product]
  apply Finset.prod_congr rfl
  intro v _
  rw [sourceKPArchComplexEquiv_norm, NumberField.IsTotallyComplex.mult_eq]
  norm_num

theorem sourceArchIwasawaDet_norm (g : GL (Fin 2) (InfiniteAdeleRing K)) (v : InfinitePlace K) :
    ‖sourceKPArchComplexEquiv K hζ v
      ((GeneralLinearGroup.det (sourceKPArchIwasawaBorel K hζ g) : InfiniteAdeleRing K) v)‖ =
        sourceArchHeight (sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)) := by
  have he (b : GL (Fin 2) (InfiniteAdeleRing K)) :
      sourceKPArchComplexEquiv K hζ v ((GeneralLinearGroup.det b : InfiniteAdeleRing K) v) =
        (GeneralLinearGroup.det (sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K b v)) : ℂ) := by
    rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two,
      GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
    change sourceKPArchComplexEquiv K hζ v (b 0 0 v*b 1 1 v-b 0 1 v*b 1 0 v) = _
    rw [map_sub, map_mul, map_mul]
    rfl
  rw [he, sourceKPArchIwasawaBorel_at, sourceArchIwasawa_torus_norm]

theorem sourceArchIwasawa_character_product (s : ℂ) (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    (sourceKPIdeleComplexNorm K (s+1/2)
      (sourceArchOnlyIdele K (GeneralLinearGroup.det (sourceKPArchIwasawaBorel K hζ g))) : ℂ) =
        ∏ v : InfinitePlace K,
          sourceArchSphericalGL s (sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)) := by
  rw [sourceArchOnlyIdele_character_complex K hζ]
  apply Finset.prod_congr rfl
  intro v _
  rw [sourceArchIwasawaDet_norm, sourceArchSphericalGL]
  congr 1
  ring

end
end ArtinMatthews
