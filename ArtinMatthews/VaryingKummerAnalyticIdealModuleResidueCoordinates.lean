module

public import ArtinMatthews.VaryingKummerAnalyticIdealModuleTrivialization
public import ArtinMatthews.VaryingKummerAnalyticRayCharacter
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! Actual residue coordinates on a fixed ideal, including the exact unit
criterion for a principal ideal in that class. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open scoped Classical
noncomputable section
variable {R : Type*} [CommRing R] [IsDedekindDomain R]

def idealResidueCoordinate (I M : Ideal R) (hI : I ≠ ⊥) (hM : M ≠ ⊥) :
    I →ₗ[R] R ⧸ M :=
  (idealModuleTrivialization I M hI hM).symm.toLinearMap.comp (idealModuleRelation I M).mkQ

theorem idealResidueCoordinate_trivialization (I M : Ideal R) (hI : I ≠ ⊥) (hM : M ≠ ⊥)
    (a : I) :
    idealModuleTrivialization I M hI hM (idealResidueCoordinate I M hI hM a) =
      Submodule.Quotient.mk a := by
  exact (idealModuleTrivialization I M hI hM).apply_symm_apply _

theorem idealResidueCoordinate_eq_mk_iff (I M : Ideal R) (hI : I ≠ ⊥) (hM : M ≠ ⊥)
    (a : I) (r : R) :
    idealResidueCoordinate I M hI hM a = Ideal.Quotient.mk M r ↔
      (a:R)-r*idealModuleGenerator I M hI hM ∈ M*I := by
  rw [← (idealModuleTrivialization I M hI hM).injective.eq_iff,
    idealResidueCoordinate_trivialization,idealModuleTrivialization_apply,
    idealModuleResidueMap_apply,Submodule.Quotient.eq]
  rfl

theorem idealResidueCoordinate_generator (I M : Ideal R) (hI : I ≠ ⊥) (hM : M ≠ ⊥) :
    idealResidueCoordinate I M hI hM
      ⟨idealModuleGenerator I M hI hM,idealModuleGenerator_mem I M hI hM⟩ = 1 := by
  rw [← map_one (Ideal.Quotient.mk M)]
  apply (idealResidueCoordinate_eq_mk_iff I M hI hM _ 1).mpr
  simp only [one_mul,sub_self,Ideal.zero_mem]

theorem idealResidueCoordinate_surjective (I M : Ideal R) (hI : I ≠ ⊥) (hM : M ≠ ⊥) :
    Function.Surjective (idealResidueCoordinate I M hI hM) :=
  (idealModuleTrivialization I M hI hM).symm.surjective.comp
    (Submodule.mkQ_surjective _)

omit [IsDedekindDomain R] in
private theorem ideal_span_sup_eq_of_sub_mem (M : Ideal R) (a b : R) (h : a-b ∈ M) :
    Ideal.span {a} ⊔ M = Ideal.span {b} ⊔ M := by
  apply le_antisymm
  · apply sup_le _ le_sup_right
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    have h1 : a-b ∈ Ideal.span {b} ⊔ M := Submodule.mem_sup_right h
    have h2 : b ∈ Ideal.span {b} ⊔ M := Submodule.mem_sup_left (Ideal.subset_span (Set.mem_singleton _))
    simpa only [sub_add_cancel] using (Ideal.span {b} ⊔ M).add_mem h1 h2
  · apply sup_le _ le_sup_right
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    have h1 : a-b ∈ Ideal.span {a} ⊔ M := Submodule.mem_sup_right h
    have h2 : a ∈ Ideal.span {a} ⊔ M := Submodule.mem_sup_left (Ideal.subset_span (Set.mem_singleton _))
    simpa only [sub_sub_cancel] using (Ideal.span {a} ⊔ M).sub_mem h2 h1

theorem idealResidueCoordinate_principal_sup (I M : Ideal R) (hI : I ≠ ⊥) (hM : M ≠ ⊥)
    (a : I) (r : R) (hr : idealResidueCoordinate I M hI hM a = Ideal.Quotient.mk M r) :
    Ideal.span {(a:R)} ⊔ M*I = (Ideal.span {r} ⊔ M)*I := by
  have hs := ideal_span_sup_eq_of_sub_mem (M*I) (a:R) (r*idealModuleGenerator I M hI hM)
    ((idealResidueCoordinate_eq_mk_iff I M hI hM a r).mp hr)
  have hg : Ideal.span {r} * I ⊔ M*I =
      Ideal.span {r*idealModuleGenerator I M hI hM} ⊔ M*I := by
    conv_lhs => lhs; rhs; rw [← idealModuleGenerator_spec I M hI hM]
    rw [Ideal.mul_sup,Ideal.span_singleton_mul_span_singleton]
    have hle : Ideal.span {r} * (M*I) ≤ M*I := Ideal.mul_le_right
    exact sup_le (sup_le (hle.trans le_sup_right) le_sup_left) le_sup_right |>.antisymm
      (sup_le (le_sup_of_le_left le_sup_right) le_sup_right)
  rw [← hg,← Ideal.sup_mul] at hs
  exact hs

theorem idealResidueCoordinate_isUnit_iff (I M : Ideal R) (hI : I ≠ ⊥) (hM : M ≠ ⊥)
    (a : I) (J : Ideal R) (hJ : Ideal.span {(a:R)} = I*J) :
    IsUnit (idealResidueCoordinate I M hI hM a) ↔ IsCoprime J M := by
  obtain ⟨r,hr⟩ := Ideal.Quotient.mk_surjective (idealResidueCoordinate I M hI hM a)
  have hs := idealResidueCoordinate_principal_sup I M hI hM a r hr.symm
  rw [hJ,mul_comm I J,← Ideal.sup_mul] at hs
  have he : J ⊔ M = Ideal.span {r} ⊔ M := mul_right_cancel₀ hI hs
  rw [← hr,quotient_isUnit_iff_span_coprime,Ideal.isCoprime_iff_sup_eq,
    Ideal.isCoprime_iff_sup_eq,← he]

end
end ArtinMatthews.VaryingKummerAnalytic
