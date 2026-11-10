module

public import ArtinMatthews.VaryingKummerAnalyticIdealModuleResidueCoordinates
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! Actual additive coset enumeration of I by I/(MI), expressed using the
proved rank-one residue trivialization. No coprimality of I and M is needed. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open scoped Classical
noncomputable section
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable (I M : Ideal R) (hI : I ≠ ⊥) (hM : M ≠ ⊥)

def idealModuleResidueRepresentative (r : R ⧸ M) : I :=
  Quotient.out (idealModuleTrivialization I M hI hM r)

theorem idealModuleResidueRepresentative_coordinate (r : R ⧸ M) :
    idealResidueCoordinate I M hI hM (idealModuleResidueRepresentative I M hI hM r) = r := by
  apply (idealModuleTrivialization I M hI hM).injective
  rw [idealResidueCoordinate_trivialization]
  exact Quotient.out_eq _

def idealModuleRelationInclusion : (M*I) →ₗ[R] I :=
  Submodule.inclusion (Ideal.mul_le_right : M*I ≤ I)

omit [IsDedekindDomain R] in
@[simp] theorem idealModuleRelationInclusion_coe (b : M*I) :
    (idealModuleRelationInclusion I M b : R) = (b : R) := rfl

theorem idealModuleRelationInclusion_coordinate (b : M*I) :
    idealResidueCoordinate I M hI hM (idealModuleRelationInclusion I M b) = 0 := by
  rw [← map_zero (Ideal.Quotient.mk M)]
  apply (idealResidueCoordinate_eq_mk_iff I M hI hM _ 0).mpr
  simpa only [zero_mul, sub_zero, idealModuleRelationInclusion_coe] using b.property

theorem idealResidueCoordinate_eq_iff_sub_mem (a b : I) :
    idealResidueCoordinate I M hI hM a = idealResidueCoordinate I M hI hM b ↔
      (a:R)-(b:R) ∈ M*I := by
  rw [← (idealModuleTrivialization I M hI hM).injective.eq_iff,
    idealResidueCoordinate_trivialization, idealResidueCoordinate_trivialization,
    Submodule.Quotient.eq]
  rfl

def idealModuleCosetEquiv : I ≃ (R ⧸ M) × (M*I) where
  toFun a := ⟨idealResidueCoordinate I M hI hM a,
    ⟨(a:R)-(idealModuleResidueRepresentative I M hI hM
      (idealResidueCoordinate I M hI hM a):R),
      (idealResidueCoordinate_eq_iff_sub_mem I M hI hM _ _).mp
        (idealModuleResidueRepresentative_coordinate I M hI hM _).symm⟩⟩
  invFun p := idealModuleResidueRepresentative I M hI hM p.1 +
    idealModuleRelationInclusion I M p.2
  left_inv a := by apply Subtype.ext; dsimp; ring
  right_inv p := by
    obtain ⟨r,b⟩ := p
    have h : idealResidueCoordinate I M hI hM
        (idealModuleResidueRepresentative I M hI hM r +
          idealModuleRelationInclusion I M b) = r := by
      rw [map_add, idealModuleResidueRepresentative_coordinate,
        idealModuleRelationInclusion_coordinate, add_zero]
    apply Prod.ext h
    apply Subtype.ext
    change ((idealModuleResidueRepresentative I M hI hM r : R) + (b:R)) -
      (idealModuleResidueRepresentative I M hI hM
        (idealResidueCoordinate I M hI hM
          (idealModuleResidueRepresentative I M hI hM r +
            idealModuleRelationInclusion I M b)) : R) = (b:R)
    rw [h]
    ring

@[simp] theorem idealModuleCosetEquiv_fst (a : I) :
    (idealModuleCosetEquiv I M hI hM a).1 = idealResidueCoordinate I M hI hM a := rfl

@[simp] theorem idealModuleCosetEquiv_symm (p : (R ⧸ M) × (M*I)) :
    (idealModuleCosetEquiv I M hI hM).symm p =
      idealModuleResidueRepresentative I M hI hM p.1 +
        idealModuleRelationInclusion I M p.2 := rfl

end
end ArtinMatthews.VaryingKummerAnalytic
