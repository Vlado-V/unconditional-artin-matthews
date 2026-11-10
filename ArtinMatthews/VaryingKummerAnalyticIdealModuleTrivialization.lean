module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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


set_option backward.privateInPublic true
@[expose] public section

/-! A fixed nonzero ideal is a free rank-one module modulo any nonzero ideal.
The generator is constructed by Dedekind ideal approximation. No coprimality
of the fixed ideal with the varying modulus is required. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open scoped Classical
noncomputable section
variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- A genuine generator of I modulo M I, with no size claim on the generator. -/
def idealModuleGenerator (I M : Ideal R) (hI : I ≠ ⊥) (hM : M ≠ ⊥) : R :=
  (IsDedekindDomain.exists_sup_span_eq (I := M*I) (J := I)
    Ideal.mul_le_right (mul_ne_zero hM hI)).choose

theorem idealModuleGenerator_spec (I M : Ideal R) (hI : I ≠ ⊥) (hM : M ≠ ⊥) :
    M*I ⊔ Ideal.span {idealModuleGenerator I M hI hM} = I :=
  (IsDedekindDomain.exists_sup_span_eq (I := M*I) (J := I)
    Ideal.mul_le_right (mul_ne_zero hM hI)).choose_spec

theorem idealModuleGenerator_mem (I M : Ideal R) (hI : I ≠ ⊥) (hM : M ≠ ⊥) :
    idealModuleGenerator I M hI hM ∈ I := by
  exact (idealModuleGenerator_spec I M hI hM).le
    (Submodule.mem_sup_right (Ideal.subset_span (Set.mem_singleton _)))

theorem idealModuleGenerator_mul_mem_iff (I M : Ideal R) (hI : I ≠ ⊥) (hM : M ≠ ⊥)
    (r : R) : r * idealModuleGenerator I M hI hM ∈ M*I ↔ r ∈ M := by
  constructor
  · intro hr
    have hmul : Ideal.span {r} * I ≤ M*I := by
      conv_lhs => rw [← idealModuleGenerator_spec I M hI hM,Ideal.mul_sup]
      apply sup_le
      · exact Ideal.mul_le_right
      · rw [Ideal.span_singleton_mul_span_singleton]
        exact (Ideal.span_singleton_le_iff_mem _).mpr hr
    have hle : Ideal.span {r} ≤ M :=
      Ideal.dvd_iff_le.mp ((mul_dvd_mul_iff_right hI).mp (Ideal.dvd_iff_le.mpr hmul))
    exact hle (Ideal.subset_span (Set.mem_singleton _))
  · intro hr
    exact Ideal.mul_mem_mul hr (idealModuleGenerator_mem I M hI hM)

def idealModuleRelation (I M : Ideal R) : Submodule R I :=
  Submodule.comap (Submodule.subtype (I : Submodule R R)) (M*I : Submodule R R)

abbrev IdealModuleResidue (I M : Ideal R) := I ⧸ idealModuleRelation I M

def idealModuleResidueMap (I M : Ideal R) (hI : I ≠ ⊥) (hM : M ≠ ⊥) :
    R →ₗ[R] IdealModuleResidue I M :=
  (idealModuleRelation I M).mkQ.comp
    (LinearMap.toSpanSingleton R I ⟨idealModuleGenerator I M hI hM,
      idealModuleGenerator_mem I M hI hM⟩)

theorem idealModuleResidueMap_apply (I M : Ideal R) (hI : I ≠ ⊥) (hM : M ≠ ⊥) (r : R) :
    idealModuleResidueMap I M hI hM r = Submodule.Quotient.mk
      (r • (⟨idealModuleGenerator I M hI hM,idealModuleGenerator_mem I M hI hM⟩ : I)) := rfl

theorem idealModuleResidueMap_ker (I M : Ideal R) (hI : I ≠ ⊥) (hM : M ≠ ⊥) :
    LinearMap.ker (idealModuleResidueMap I M hI hM) = M := by
  ext r
  rw [LinearMap.mem_ker,idealModuleResidueMap_apply,Submodule.Quotient.mk_eq_zero]
  exact idealModuleGenerator_mul_mem_iff I M hI hM r

theorem idealModuleResidueMap_surjective (I M : Ideal R) (hI : I ≠ ⊥) (hM : M ≠ ⊥) :
    Function.Surjective (idealModuleResidueMap I M hI hM) := by
  intro y
  induction y using Submodule.Quotient.induction_on with
  | H y =>
    have hy := (idealModuleGenerator_spec I M hI hM).ge y.property
    rw [Submodule.mem_sup] at hy
    obtain ⟨a,ha,b,hb,hab⟩ := hy
    obtain ⟨r,hr⟩ := Ideal.mem_span_singleton.mp hb
    refine ⟨r,?_⟩
    rw [idealModuleResidueMap_apply]
    apply (Submodule.Quotient.eq _).mpr
    change (r*idealModuleGenerator I M hI hM-(y:R)) ∈ M*I
    have he : r*idealModuleGenerator I M hI hM-(y:R) = -a := by
      rw [mul_comm,← hr,← hab]
      ring
    rw [he]
    exact (M*I).neg_mem ha

/-- The actual module equivalence R/M ≃ I/(MI). It works for fixed I and all
nonzero M, including moduli sharing prime divisors with I. -/
def idealModuleTrivialization (I M : Ideal R) (hI : I ≠ ⊥) (hM : M ≠ ⊥) :
    (R ⧸ M) ≃ₗ[R] IdealModuleResidue I M :=
  (Submodule.quotEquivOfEq M (LinearMap.ker (idealModuleResidueMap I M hI hM))
    (idealModuleResidueMap_ker I M hI hM).symm).trans
      ((idealModuleResidueMap I M hI hM).quotKerEquivOfSurjective
        (idealModuleResidueMap_surjective I M hI hM))

theorem idealModuleTrivialization_apply (I M : Ideal R) (hI : I ≠ ⊥) (hM : M ≠ ⊥) (r : R) :
    idealModuleTrivialization I M hI hM (Ideal.Quotient.mk M r) =
      idealModuleResidueMap I M hI hM r := by
  change idealModuleTrivialization I M hI hM (Submodule.Quotient.mk r) = _
  simp only [idealModuleTrivialization,LinearEquiv.trans_apply,Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

end
end ArtinMatthews.VaryingKummerAnalytic
