module

public import ArtinMatthews.SixthExteriorPowerClasses
public import Mathlib.NumberTheory.NumberField.ClassNumber
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

/-! An actual finite exceptional set making every fractional ideal
principal outside that set. It is constructed from the supports of integral
representatives of the finite ideal class group, rather than supplied as
an S-principality hypothesis. -/
namespace ArtinMatthews
open IsDedekindDomain NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def exteriorFractionalSupport (I : FractionalIdeal (𝓞 K)⁰ K) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors I)).toFinset

@[simp] theorem mem_exteriorFractionalSupport (I : FractionalIdeal (𝓞 K)⁰ K)
    (p : HeightOneSpectrum (𝓞 K)) :
    p ∈ exteriorFractionalSupport I ↔ FractionalIdeal.count K p I ≠ 0 := by
  simp only [exteriorFractionalSupport,Set.Finite.mem_toFinset,Set.mem_ofPred_eq]

def exteriorClassRepresentative (c : ClassGroup (𝓞 K)) : (Ideal (𝓞 K))⁰ :=
  (ClassGroup.mk0_surjective c).choose

@[simp] theorem exteriorClassRepresentative_class (c : ClassGroup (𝓞 K)) :
    ClassGroup.mk0 (exteriorClassRepresentative c)=c :=
  (ClassGroup.mk0_surjective c).choose_spec

def exteriorPrincipalizingPrimes (K : Type*) [Field K] [NumberField K] :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  Finset.univ.biUnion fun c : ClassGroup (𝓞 K) =>
    exteriorFractionalSupport (FractionalIdeal.mk0 K (exteriorClassRepresentative c))

theorem exteriorClassRepresentative_count_eq_zero
    (c : ClassGroup (𝓞 K)) (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∉ exteriorPrincipalizingPrimes K) :
    FractionalIdeal.count K p (FractionalIdeal.mk0 K (exteriorClassRepresentative c))=0 := by
  by_contra h
  apply hp
  exact Finset.mem_biUnion.mpr ⟨c,Finset.mem_univ _,
    (mem_exteriorFractionalSupport _ p).mpr h⟩

theorem principalFractionalIdeal_mem_range_of_class_one
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hI : ClassGroup.mk K I=1) :
    I ∈ (toPrincipalIdeal (𝓞 K) K).range := by
  have h := congrArg (ClassGroup.equiv K) hI
  have hrefl : Units.mapEquiv (MulEquiv.refl (FractionalIdeal (𝓞 K)⁰ K)) I=I :=
    Units.ext rfl
  simpa only [ClassGroup.equiv_mk,FractionalIdeal.canonicalEquiv_self,
    RingEquiv.coe_mulEquiv_refl,hrefl,map_one,
    QuotientGroup.mk'_apply,QuotientGroup.eq_one_iff] using h

/-- Every actual fractional ideal has a field generator with the same
prime exponents outside the constructed finite class-support set. -/
theorem exists_principal_generator_outside_class_support
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ t : Kˣ, ∀ p : HeightOneSpectrum (𝓞 K), p ∉ exteriorPrincipalizingPrimes K →
      exteriorPrincipalValuation p t=FractionalIdeal.count K p (I:FractionalIdeal (𝓞 K)⁰ K) := by
  let J := FractionalIdeal.mk0 K (exteriorClassRepresentative (ClassGroup.mk K I))
  have hJ : ClassGroup.mk K J=ClassGroup.mk K I := by
    rw [ClassGroup.mk_mk0,exteriorClassRepresentative_class]
  have hclass : ClassGroup.mk K (I/J)=1 := by rw [map_div,hJ]; simp
  obtain ⟨t,ht⟩ := principalFractionalIdeal_mem_range_of_class_one (I/J) hclass
  refine ⟨t,?_⟩
  intro p hp
  have hzero : FractionalIdeal.count K p (J:FractionalIdeal (𝓞 K)⁰ K)=0 :=
    exteriorClassRepresentative_count_eq_zero _ p hp
  have h := congrArg (fun A : (FractionalIdeal (𝓞 K)⁰ K)ˣ =>
    FractionalIdeal.count K p (A:FractionalIdeal (𝓞 K)⁰ K)) ht
  change exteriorPrincipalValuation p t=
    FractionalIdeal.count K p ((I:FractionalIdeal (𝓞 K)⁰ K) * (J:FractionalIdeal (𝓞 K)⁰ K)⁻¹) at h
  rw [FractionalIdeal.count_mul K p I.ne_zero (inv_ne_zero J.ne_zero),
    FractionalIdeal.count_inv,hzero,neg_zero,add_zero] at h
  exact h

end
end ArtinMatthews
