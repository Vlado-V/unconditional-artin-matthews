module

public import ArtinMatthews.SourceKPAdelicCompactSplit
public import ArtinMatthews.SourceKPAdelicUnitTorus
public import ArtinMatthews.SourceKPAdelicTorusUpper
public import ArtinMatthews.SourceKPCompactBorelPhase
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

/-! The phase-one matrix section and the exact normalization of its
compact triangular representatives. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicMatrixLift (g : GL (Fin 2) 𝔸[K]) : SourceKPAdelicProjective K hζ :=
  (ProjGenLinGroup.mk ((sourceKPGL2ProductEquiv K g).1),
    sourceKPFiniteAdeleProjectiveLift K hζ ((sourceKPGL2ProductEquiv K g).2))

theorem sourceKPAdelicMatrixLift_projection (g : GL (Fin 2) 𝔸[K]) :
    sourceKPAdelicProjectiveProjection K hζ (sourceKPAdelicMatrixLift K hζ g) =
      ProjGenLinGroup.mk g := by
  apply (sourceKPAdelicProjectiveProductEquiv K).injective
  rw [sourceKPAdelicProjectiveProjection_product]
  rfl

theorem sourceKPAdelicMatrixLift_deepCompact (g : sourceKPAdelicDeepCompactMatrix K hζ) :
    sourceKPAdelicMatrixLift K hζ g.val = sourceKPAdelicDeepCompactLift K hζ g := rfl

theorem sourceKPGL2ProductEquiv_upper (x : 𝔸[K]) :
    sourceKPGL2ProductEquiv K (sourceKPUpperMatrix 𝔸[K] x) =
      (sourceKPUpperMatrix (InfiniteAdeleRing K) x.1, sourceKPUpperMatrix 𝔸ᶠ[K] x.2) := by
  apply Prod.ext <;> apply GeneralLinearGroup.ext <;> intro i j <;>
    fin_cases i <;> fin_cases j <;> rfl

theorem sourceKPGL2ProductEquiv_diagonal (a : IdeleGroup (𝓞 K) K) :
    sourceKPGL2ProductEquiv K (sourceKPDiagonalHom 𝔸[K] a) =
      (sourceKPDiagonalHom (InfiniteAdeleRing K) (sourceKPIdeleInfiniteUnit K a),
        sourceKPDiagonalHom 𝔸ᶠ[K] (sourceKPIdeleFiniteUnit K a)) := by
  apply Prod.ext <;> apply GeneralLinearGroup.ext <;> intro i j <;>
    fin_cases i <;> fin_cases j <;> rfl

theorem sourceKPAdelicMatrixLift_upper_diagonal (x : 𝔸[K]) (a : IdeleGroup (𝓞 K) K) :
    sourceKPAdelicMatrixLift K hζ (sourceKPUpperMatrix 𝔸[K] x * sourceKPDiagonalHom 𝔸[K] a) =
      sourceKPAdelicUpperLift K hζ x * sourceKPAdelicProjectiveDiagonalLift K hζ a := by
  apply Prod.ext
  · change ProjGenLinGroup.mk ((sourceKPGL2ProductEquiv K
        (sourceKPUpperMatrix 𝔸[K] x * sourceKPDiagonalHom 𝔸[K] a)).1) = _
    rw [map_mul, sourceKPGL2ProductEquiv_upper, sourceKPGL2ProductEquiv_diagonal]
    exact map_mul ProjGenLinGroup.mk _ _
  · change sourceKPFiniteAdeleProjectiveLift K hζ ((sourceKPGL2ProductEquiv K
        (sourceKPUpperMatrix 𝔸[K] x * sourceKPDiagonalHom 𝔸[K] a)).2) = _
    rw [map_mul, sourceKPGL2ProductEquiv_upper, sourceKPGL2ProductEquiv_diagonal]
    change sourceKPFiniteAdeleProjectiveLift K hζ
      (sourceKPUpperMatrix 𝔸ᶠ[K] x.2 * sourceKPDiagonalHom 𝔸ᶠ[K] (sourceKPIdeleFiniteUnit K a)) = _
    rw [
      ← sourceKPFiniteAdeleProjectiveLift_mul_of_phase_one K hζ _ _
        (sourceKPAdeleMultiplier_upper_diagonal K hζ (sourceKPIdeleFiniteUnit K a) x.2)]
    rfl

theorem sourceKPAdelicMatrixLift_normalized_scalar
    (b : GL (Fin 2) 𝔸[K]) (hb : b ∈ sourceKPRingNormalizedBorel 𝔸[K])
    (u : IdeleGroup (𝓞 K) K)
    (hu : ∀ P, sourceKPFiniteVal K P
      (sourceKPIdeleFiniteCoordinate K P u : P.adicCompletion K) = 1)
    (hbval : ∀ P, sourceKPFiniteVal K P
      (GeneralLinearGroup.det (sourceKPAdelicBaseFiniteAt K P b) : P.adicCompletion K) = 1)
    (huc : ∀ P, (6 : 𝓞 K) ∈ P.asIdeal →
      sourceKPIdeleFiniteCoordinate K P u ∈ sourceKPUnitCubes (P.adicCompletion K)) :
    sourceKPAdelicMatrixLift K hζ (b * GeneralLinearGroup.scalar (Fin 2) u) =
      sourceKPAdelicMatrixLift K hζ b := by
  apply Prod.ext
  · change ProjGenLinGroup.mk ((sourceKPGL2ProductEquiv K
        (b * GeneralLinearGroup.scalar (Fin 2) u)).1) = _
    rw [map_mul, sourceKPGL2ProductEquiv_scalar]
    change ProjGenLinGroup.mk ((sourceKPGL2ProductEquiv K b).1 *
      GeneralLinearGroup.scalar (Fin 2) (sourceKPIdeleInfiniteUnit K u)) = _
    rw [map_mul, ProjGenLinGroup.mk_scalar, mul_one]
    rfl
  · change sourceKPFiniteAdeleProjectiveLift K hζ ((sourceKPGL2ProductEquiv K
        (b * GeneralLinearGroup.scalar (Fin 2) u)).2) = _
    rw [map_mul, sourceKPGL2ProductEquiv_scalar]
    change sourceKPFiniteAdeleProjectiveLift K hζ ((sourceKPGL2ProductEquiv K b).2 *
      GeneralLinearGroup.scalar (Fin 2) (sourceKPIdeleFiniteUnit K u)) = _
    have hbf : (sourceKPGL2ProductEquiv K b).2 ∈
        sourceKPRingNormalizedBorel 𝔸ᶠ[K] := by
      constructor
      · change (b 1 0).2 = 0
        rw [hb.1]
        rfl
      · change (b 1 1).2 = 1
        rw [hb.2]
        rfl
    exact sourceKPFiniteAdeleProjectiveLift_normalized_scalar K hζ _ hbf
      (sourceKPIdeleFiniteUnit K u) hu hbval huc

end
end ArtinMatthews
