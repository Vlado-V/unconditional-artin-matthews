module

public import ArtinMatthews.SourceKPAdelicHeight
public import ArtinMatthews.SourceFiniteIwasawaHeight
public import ArtinMatthews.SourceKPAdelicCompactIntersection
public import ArtinMatthews.SourceKPLocalMatrixHeight
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

/-! Iwasawa height of an actual Borel–scalar–compact factorization. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicBaseFiniteAt_normalized (P : HeightOneSpectrum (𝓞 K))
    (b : GL (Fin 2) 𝔸[K]) (hb : b ∈ sourceKPRingNormalizedBorel 𝔸[K]) :
    sourceKPAdelicBaseFiniteAt K P b ∈ sourceGL2NormalizedBorel (P.adicCompletion K) := by
  constructor
  · change (b 1 0).2 P = 0
    rw [hb.1]
    rfl
  · change (b 1 1).2 P = 1
    rw [hb.2]
    rfl

theorem sourceKPAdelicBaseComplexAt_normalized (v : InfinitePlace K)
    (b : GL (Fin 2) 𝔸[K]) (hb : b ∈ sourceKPRingNormalizedBorel 𝔸[K]) :
    sourceKPAdelicBaseComplexAt K hζ v b ∈ sourceGL2NormalizedBorel ℂ := by
  constructor
  · change sourceKPArchComplexEquiv K hζ v ((b 1 0).1 v) = 0
    rw [hb.1]
    exact map_zero _
  · change sourceKPArchComplexEquiv K hζ v ((b 1 1).1 v) = 1
    rw [hb.2]
    exact map_one _

theorem sourceKPAdelicBaseFiniteAt_scalar (P : HeightOneSpectrum (𝓞 K))
    (u : IdeleGroup (𝓞 K) K) :
    sourceKPAdelicBaseFiniteAt K P (GeneralLinearGroup.scalar (Fin 2) u) =
      GeneralLinearGroup.scalar (Fin 2) (sourceKPIdeleFiniteCoordinate K P u) := by
  change sourceKPAdeleMatrixAt K P ((sourceKPGL2ProductEquiv K
    (GeneralLinearGroup.scalar (Fin 2) u)).2) = _
  rw [sourceKPGL2ProductEquiv_scalar]
  exact sourceKPAdeleMatrixAt_scalar K P _

theorem sourceKPAdelicBaseComplexAt_scalar (v : InfinitePlace K)
    (u : IdeleGroup (𝓞 K) K) :
    sourceKPAdelicBaseComplexAt K hζ v (GeneralLinearGroup.scalar (Fin 2) u) =
      GeneralLinearGroup.scalar (Fin 2)
        (Units.map (sourceKPArchComplexEquiv K hζ v) (sourceKPIdeleInfiniteCoordinate K v u)) := by
  change sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K
    ((sourceKPGL2ProductEquiv K (GeneralLinearGroup.scalar (Fin 2) u)).1) v) = _
  rw [sourceKPGL2ProductEquiv_scalar]
  change sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K
    (GeneralLinearGroup.scalar (Fin 2) (sourceKPIdeleInfiniteUnit K u)) v) = _
  rw [sourceArchGLPiEquiv_scalar, sourceKPArchMatrixComplexEquiv_scalar]
  rfl

theorem sourceArchHeight_borel_scalar_unitary (b : GL (Fin 2) ℂ)
    (hb : b ∈ sourceGL2NormalizedBorel ℂ) (u : ℂˣ) (k : Matrix.unitaryGroup (Fin 2) ℂ) :
    sourceArchHeight (b * GeneralLinearGroup.scalar (Fin 2) u * sourceArchUnitaryGL k) =
      ‖(GeneralLinearGroup.det b : ℂ)‖ := by
  rw [sourceArchHeight_unitary, sourceArchHeight_scalar]
  have he := sourceArchHeight_borel b 1 hb
  simpa [sourceArchHeight, sourceArchBottomNorm] using he

theorem sourceKPAdelicHeight_factor (g b k : GL (Fin 2) 𝔸[K])
    (u : IdeleGroup (𝓞 K) K) (hb : b ∈ sourceKPRingNormalizedBorel 𝔸[K])
    (hk : k ∈ SourceKPAdelicBaseCompactMatrix K hζ)
    (he : g = b * GeneralLinearGroup.scalar (Fin 2) u * k) :
    sourceKPAdelicHeight K hζ g = sourceKPIdeleAbsoluteNorm K (GeneralLinearGroup.det b) := by
  change sourceKPAdelicHeight K hζ g =
    ‖(sourceKPIdeleInfiniteUnit K (GeneralLinearGroup.det b) : InfiniteAdeleRing K)‖ *
      ‖(sourceKPIdeleFiniteUnit K (GeneralLinearGroup.det b) : 𝔸ᶠ[K])‖
  rw [sourceKPAdelicHeight_product, InfiniteAdeleRing.norm_def,
    FiniteAdeleRing.norm_eq_finprod_of_unit]
  congr 1
  · apply Finset.prod_congr rfl
    intro v _
    change sourceArchHeight (sourceKPAdelicBaseComplexAt K hζ v g) ^ v.mult =
      ‖(sourceKPIdeleInfiniteCoordinate K v (GeneralLinearGroup.det b) : v.Completion)‖ ^ v.mult
    rw [← sourceKPArchComplexEquiv_norm K hζ v, sourceKPAdelicComplexCoordinate_det]
    congr 1
    obtain ⟨k₀,hk₀⟩ := hk.2 v
    have hv := congrArg (sourceKPAdelicBaseComplexAt K hζ v) he
    rw [map_mul, map_mul, sourceKPAdelicBaseComplexAt_scalar, ← hk₀] at hv
    rw [hv]
    exact sourceArchHeight_borel_scalar_unitary _ (sourceKPAdelicBaseComplexAt_normalized K hζ v b hb) _ _
  · apply finprod_congr
    intro P
    change sourceKPFiniteMatrixHeight K P (sourceKPAdelicBaseFiniteAt K P g) =
      ‖(sourceKPIdeleFiniteCoordinate K P (GeneralLinearGroup.det b) : P.adicCompletion K)‖
    rw [sourceKPAdelicFiniteCoordinate_det]
    have hP := congrArg (sourceKPAdelicBaseFiniteAt K P) he
    rw [map_mul, map_mul, sourceKPAdelicBaseFiniteAt_scalar] at hP
    exact (sourceKPIwasawa_torus_norm K P _ _ _ _
      (sourceKPAdelicBaseFiniteAt_normalized K P b hb) (hk.1 P) hP).symm

theorem sourceKPAdelicHeight_projective (g h : GL (Fin 2) 𝔸[K])
    (he : ProjGenLinGroup.mk g = ProjGenLinGroup.mk h) :
    sourceKPAdelicHeight K hζ g = sourceKPAdelicHeight K hζ h := by
  obtain ⟨u,hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp he
  let b := sourceKPAdelicIwasawaBorel K hζ g
  let k := sourceKPAdelicIwasawaCompact K hζ g
  let d := sourceKPAdelicIwasawaScalar K hζ g
  have hh : h = b * GeneralLinearGroup.scalar (Fin 2) (d*u) * k := by
    rw [← hu, sourceKPAdelicIwasawa_factor K hζ g]
    change (b * GeneralLinearGroup.scalar (Fin 2) d * k) * GeneralLinearGroup.scalar (Fin 2) u = _
    calc
      _ = (b * GeneralLinearGroup.scalar (Fin 2) d) *
          (k * GeneralLinearGroup.scalar (Fin 2) u) := mul_assoc _ _ _
      _ = (b * GeneralLinearGroup.scalar (Fin 2) d) *
          (GeneralLinearGroup.scalar (Fin 2) u * k) := by rw [← GeneralLinearGroup.scalar_commute u k]
      _ = (b * (GeneralLinearGroup.scalar (Fin 2) d * GeneralLinearGroup.scalar (Fin 2) u)) * k := by
        simp only [mul_assoc]
      _ = _ := by rw [← map_mul]
  have heh := sourceKPAdelicHeight_factor K hζ h b k (d*u)
    (sourceKPAdelicIwasawaBorel_mem K hζ g) (sourceKPAdelicIwasawaCompact_mem K hζ g) hh
  exact heh.symm

end
end ArtinMatthews
