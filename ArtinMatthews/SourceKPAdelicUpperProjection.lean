module

public import ArtinMatthews.SourceKPAdelicUpper
public import ArtinMatthews.SourceKPAdelicRationalSum
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

theorem sourceKPUpperMatrix_projective_injective (R : Type*) [CommRing R] :
    Function.Injective (fun x : R => ProjGenLinGroup.mk (sourceKPUpperMatrix R x)) := by
  intro x y h
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
  have h11 := congrArg (fun g : GL (Fin 2) R => g 1 1) hu
  have hunit : u = 1 := by
    apply Units.ext
    simpa [sourceKPMatrix_right_scalar_entry, sourceKPUpperMatrix] using h11
  rw [hunit, map_one, mul_one] at hu
  have h01 := congrArg (fun g : GL (Fin 2) R => g 0 1) hu
  exact h01

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicUpperHom : Multiplicative 𝔸[K] →* SourceKPAdelicProjective K hζ where
  toFun x := sourceKPAdelicUpperLift K hζ x.toAdd
  map_one' := sourceKPAdelicUpperLift_zero K hζ
  map_mul' x y := sourceKPAdelicUpperLift_add K hζ x.toAdd y.toAdd

theorem sourceKPAdelicUpperLift_projection (x : 𝔸[K]) :
    sourceKPAdelicProjectiveProjection K hζ (sourceKPAdelicUpperLift K hζ x) =
      ProjGenLinGroup.mk (sourceKPUpperMatrix 𝔸[K] x) := by
  apply (sourceKPAdelicProjectiveProductEquiv K).injective
  rw [sourceKPAdelicProjectiveProjection_product]
  change (ProjGenLinGroup.mk (sourceKPUpperMatrix (InfiniteAdeleRing K) x.1),
    ProjGenLinGroup.mk (sourceKPUpperMatrix 𝔸ᶠ[K] x.2)) =
    (ProjGenLinGroup.mk (GeneralLinearGroup.map (sourceKPAdeleInfiniteProjection K)
      (sourceKPUpperMatrix 𝔸[K] x)),
      ProjGenLinGroup.mk (GeneralLinearGroup.map (sourceKPAdeleFiniteProjection K)
      (sourceKPUpperMatrix 𝔸[K] x)))
  apply Prod.ext
  · exact (congrArg (ProjGenLinGroup.mk (n := Fin 2) (R := InfiniteAdeleRing K))
      (sourceKPUpperMatrix_map (sourceKPAdeleInfiniteProjection K) x)).symm
  · exact (congrArg (ProjGenLinGroup.mk (n := Fin 2) (R := 𝔸ᶠ[K]))
      (sourceKPUpperMatrix_map (sourceKPAdeleFiniteProjection K) x)).symm

theorem sourceKPAdelicUpperLift_injective : Function.Injective (sourceKPAdelicUpperLift K hζ) := by
  intro x y h
  apply sourceKPUpperMatrix_projective_injective 𝔸[K]
  change ProjGenLinGroup.mk (sourceKPUpperMatrix 𝔸[K] x) =
    ProjGenLinGroup.mk (sourceKPUpperMatrix 𝔸[K] y)
  rw [← sourceKPAdelicUpperLift_projection K hζ x, ← sourceKPAdelicUpperLift_projection K hζ y, h]

theorem sourceKPAdelicRationalSum_canonical_bruhat
    (f : SourceKPRationalBorelFunction K hζ) (g : SourceKPAdelicProjective K hζ)
    (hs : Summable (sourceKPAdelicRationalSummand K hζ f g)) :
    sourceKPAdelicRationalSum K hζ f g = f.val g +
      ∑' x : K, f.val (sourceKPAdelicProjectiveWeyl K hζ *
        sourceKPAdelicUpperLift K hζ (algebraMap K 𝔸[K] x) * g) := by
  simp_rw [sourceKPAdelicUpperLift_rational]
  exact sourceKPAdelicRationalSum_bruhat K hζ f g hs

end
end ArtinMatthews
