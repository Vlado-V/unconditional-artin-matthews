module

public import ArtinMatthews.SourceCRTInverseCofactor
public import ArtinMatthews.SourceCRTKernel
public import ArtinMatthews.SourceProductUnits
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

/-! The literal finite-F CRT phase, after passing to the product of its
outer and inner local ideals, retains exactly the inverse cofactor. -/
namespace ArtinMatthews.SourceCRTNormalization

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem sourceSexticCRTPhase_eq (P : ι → HeightOneSpectrum (𝓞 K))
    (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (k t : ι → ℕ) :
    sourceSexticCRTPhase S₀ P a ha k t =
      sourceCRTPhase S₀ P (fun j => k j + t j) (∏ j, a j ^ (k j + t j))
        (generatorProduct_ne_zero S₀ P a ha (fun j => k j + t j))
        (crtModulus_generator S₀ P (fun j => k j + t j) a ha) := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  unfold sourceSexticCRTPhase
  rw [sourceCRTPhase_mk, sourceCRTPhase_mk]
  have he : (∏ j, a j ^ k j) * (∏ j, a j ^ t j) = ∏ j, a j ^ (k j + t j) := by
    simp only [pow_add, Finset.prod_mul_distrib]
  rw [he]

theorem sourcePrimeCofactor_add (a : ι → PrincipalIntegerRing S₀) (k t : ι → ℕ) (i : ι) :
    sourcePrimeCofactor S₀ a (fun j => k j + t j) i =
      sourcePrimeCofactor S₀ a k i * sourcePrimeCofactor S₀ a t i := by
  simp only [sourcePrimeCofactor, pow_add, Finset.prod_mul_distrib]

def sourceProductInverseCofactor (P : ι → HeightOneSpectrum (𝓞 K))
    (hP : Pairwise fun i j => P i ≠ P j) (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (k t : ι → ℕ) (i : ι) :
    ((PrincipalIntegerRing S₀) ⧸ (primePowerIdeal S₀ (P i) (k i) * primePowerIdeal S₀ (P i) (t i)))ˣ :=
  Units.map (Ideal.quotEquivOfEq (primePowerIdeal_add S₀ (P i) (k i) (t i))).toMonoidHom
    ((sourcePrimeCofactorUnit S₀ P hP a ha (fun j => k j + t j) i)⁻¹)

theorem sourceCRTProductPhase_eq_inverseShift (P : ι → HeightOneSpectrum (𝓞 K))
    (hP : Pairwise fun i j => P i ≠ P j) (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (k t : ι → ℕ) (i : ι) :
    sourceCRTProductPhase S₀ P k t hP (sourceSexticCRTPhase S₀ P a ha k t) i =
      (sourceLocalProductPhase S₀ (P i) (a i) (ha i) (k i) (t i)).mulShift
        (sourceProductInverseCofactor S₀ P hP a ha k t i) := by
  rw [sourceSexticCRTPhase_eq]
  let e := Ideal.quotEquivOfEq (primePowerIdeal_add S₀ (P i) (k i) (t i))
  let u := sourcePrimeCofactorUnit S₀ P hP a ha (fun j => k j + t j) i
  ext x
  change sourcePrimeComponent S₀ P hP a ha (fun j => k j + t j) i (e.symm x) =
    sourcePrimePowerPhase S₀ (P i) (a i) (ha i) (k i + t i)
      (e.symm ((sourceProductInverseCofactor S₀ P hP a ha k t i :
        (PrincipalIntegerRing S₀) ⧸ (primePowerIdeal S₀ (P i) (k i) * primePowerIdeal S₀ (P i) (t i))) * x))
  rw [sourcePrimeComponent_eq_inverseShift, AddChar.mulShift_apply]
  congr 1
  rw [e.symm.map_mul]
  change (u⁻¹ : ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (k i + t i))ˣ) * e.symm x =
    e.symm (e (u⁻¹ : ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (k i + t i))ˣ)) * e.symm x
  rw [e.symm_apply_apply]

end
end ArtinMatthews.SourceCRTNormalization
