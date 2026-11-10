module

public import ArtinMatthews.SourceCRTCofactorPhase
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

/-! The cofactor appearing in the actual standard CRT component is a
unit of the exact prime-power quotient, including the zero modulus. -/
namespace ArtinMatthews.SourceCRTNormalization

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.StandardAdelic
open ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sourcePrimeCofactor_coprime (P : ι → HeightOneSpectrum (𝓞 K))
    (hP : Pairwise fun i j => P i ≠ P j) (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (n : ι → ℕ) (i : ι) : IsCoprime (a i ^ n i) (sourcePrimeCofactor S₀ a n i) := by
  apply IsCoprime.prod_right
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  have hc := primePowerIdeal_pairwise S₀ P n hP hji.symm
  change IsCoprime (primePowerIdeal S₀ (P i) (n i)) (primePowerIdeal S₀ (P j) (n j)) at hc
  rw [primePowerIdeal, primePowerIdeal, generator_power_ideal S₀ (P i) (a i) (ha i),
    generator_power_ideal S₀ (P j) (a j) (ha j), Ideal.isCoprime_span_singleton_iff] at hc
  exact hc

theorem sourcePrimeCofactor_isUnit (P : ι → HeightOneSpectrum (𝓞 K))
    (hP : Pairwise fun i j => P i ≠ P j) (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (n : ι → ℕ) (i : ι) :
    IsUnit (Ideal.Quotient.mk (primePowerIdeal S₀ (P i) (n i)) (sourcePrimeCofactor S₀ a n i)) := by
  obtain ⟨u, v, h⟩ := sourcePrimeCofactor_coprime S₀ P hP a ha n i
  have hz : Ideal.Quotient.mk (primePowerIdeal S₀ (P i) (n i)) (a i ^ n i) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [primePowerIdeal, generator_power_ideal S₀ (P i) (a i) (ha i)]
    exact Ideal.mem_span_singleton_self _
  apply isUnit_iff_dvd_one.mpr
  refine ⟨Ideal.Quotient.mk _ v, ?_⟩
  have he := congrArg (Ideal.Quotient.mk (primePowerIdeal S₀ (P i) (n i))) h
  simpa only [map_add, map_mul, map_one, hz, mul_zero, zero_mul, zero_add, mul_comm] using he.symm

def sourcePrimeCofactorUnit (P : ι → HeightOneSpectrum (𝓞 K))
    (hP : Pairwise fun i j => P i ≠ P j) (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (n : ι → ℕ) (i : ι) : ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (n i))ˣ :=
  (sourcePrimeCofactor_isUnit S₀ P hP a ha n i).choose

theorem sourcePrimeCofactorUnit_val (P : ι → HeightOneSpectrum (𝓞 K))
    (hP : Pairwise fun i j => P i ≠ P j) (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (n : ι → ℕ) (i : ι) :
    (sourcePrimeCofactorUnit S₀ P hP a ha n i : (PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (n i)) =
      Ideal.Quotient.mk _ (sourcePrimeCofactor S₀ a n i) :=
  (sourcePrimeCofactor_isUnit S₀ P hP a ha n i).choose_spec

theorem sourcePrimeComponent_mulShift (P : ι → HeightOneSpectrum (𝓞 K))
    (hP : Pairwise fun i j => P i ≠ P j) (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (n : ι → ℕ) (i : ι) :
    (sourcePrimeComponent S₀ P hP a ha n i).mulShift
        (sourcePrimeCofactorUnit S₀ P hP a ha n i) =
      sourcePrimePowerPhase S₀ (P i) (a i) (ha i) (n i) := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [AddChar.mulShift_apply, sourcePrimeCofactorUnit_val, ← map_mul]
  exact sourcePrimeComponent_on_cofactor S₀ P hP a ha n i x

theorem sourcePrimeComponent_eq_inverseShift (P : ι → HeightOneSpectrum (𝓞 K))
    (hP : Pairwise fun i j => P i ≠ P j) (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (n : ι → ℕ) (i : ι) :
    sourcePrimeComponent S₀ P hP a ha n i =
      (sourcePrimePowerPhase S₀ (P i) (a i) (ha i) (n i)).mulShift
        ((sourcePrimeCofactorUnit S₀ P hP a ha n i)⁻¹ :
          ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (n i))ˣ) := by
  let u := sourcePrimeCofactorUnit S₀ P hP a ha n i
  have hc : (u : (PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (n i)) * (u⁻¹ :
      ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (n i))ˣ) = 1 := by
    simpa only [Units.val_mul, Units.val_one] using
      congrArg (fun z : ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (n i))ˣ =>
        (z : (PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (n i))) (mul_inv_cancel u)
  ext x
  have hs : (sourcePrimeComponent S₀ P hP a ha n i).mulShift (u :
      (PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (n i)) =
      sourcePrimePowerPhase S₀ (P i) (a i) (ha i) (n i) := sourcePrimeComponent_mulShift S₀ P hP a ha n i
  have he := congrArg (fun ψ : AddChar ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (n i)) ℂ =>
      ψ ((u⁻¹ : ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (n i))ˣ) * x))
    hs
  change sourcePrimeComponent S₀ P hP a ha n i x =
    (sourcePrimePowerPhase S₀ (P i) (a i) (ha i) (n i)).mulShift
      ((u⁻¹ : ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (n i))ˣ) :
        (PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (n i)) x
  simpa only [AddChar.mulShift_apply, ← mul_assoc, hc, one_mul] using he

end
end ArtinMatthews.SourceCRTNormalization
