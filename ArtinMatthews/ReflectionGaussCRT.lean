module

public import ArtinMatthews.SourceCRTInverseCofactor
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

/-! The many-prime Gauss expansion in the actual S-integer source phase.
Every directed cofactor character is retained. No phase compatibility
or multiplicativity of the normalized quadratic Gauss sum is assumed. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField IsDedekindDomain SIntegerPrincipalization SIntegerQuotient
open StandardAdelic SourceCRTNormalization
open scoped NumberField Classical BigOperators
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem reflectionCRTGauss_factor
    (P : ι → HeightOneSpectrum (𝓞 K)) (hP : Pairwise fun i j => P i ≠ P j)
    (hS : ∀ i, P i ∉ principalizingSet S₀) (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (n : ι → ℕ)
    (χ : ∀ i, MulChar ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (n i)) ℂ) :
    (∑' x : (PrincipalIntegerRing S₀) ⧸ crtModulus S₀ P n,
      (∏ i, χ i (primeCRTEquiv S₀ P n hP x i)) *
        sourceCRTPhase S₀ P n (∏ i, a i ^ n i) (generatorProduct_ne_zero S₀ P a ha n)
          (crtModulus_generator S₀ P n a ha) x) =
      ∏ i, ∑' x : (PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (n i),
        χ i x * sourcePrimeComponent S₀ P hP a ha n i x := by
  let R := fun i => (PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (n i)
  let E := primeCRTEquiv S₀ P n hP
  let Ψ := sourceCRTPhase S₀ P n (∏ i, a i ^ n i)
    (generatorProduct_ne_zero S₀ P a ha n) (crtModulus_generator S₀ P n a ha)
  let : Finite ((PrincipalIntegerRing S₀) ⧸ crtModulus S₀ P n) := crtQuotient_finite S₀ P n hP hS
  let := Fintype.ofFinite ((PrincipalIntegerRing S₀) ⧸ crtModulus S₀ P n)
  let : ∀ i, Finite (R i) := fun i => primePowerQuotient_finite S₀ (P i) (hS i) (n i)
  let : ∀ i, Fintype (R i) := fun _ => Fintype.ofFinite _
  have hphase (x : (PrincipalIntegerRing S₀) ⧸ crtModulus S₀ P n) :
      Ψ x = ∏ i, sourcePrimeComponent S₀ P hP a ha n i (E x i) :=
    probeCRTAddChar_factor R E Ψ x
  simp only [tsum_fintype]
  rw [← E.symm.toEquiv.sum_comp]
  calc
    _ = ∑ x : ∀ i, R i, ∏ i,
        χ i (x i) * sourcePrimeComponent S₀ P hP a ha n i (x i) := by
      apply Finset.sum_congr rfl
      intro x _
      have he := E.apply_symm_apply x
      rw [hphase]
      change (∏ i, χ i (E (E.symm x) i)) *
        (∏ i, sourcePrimeComponent S₀ P hP a ha n i (E (E.symm x) i)) = _
      rw [he, Finset.prod_mul_distrib]
    _ = _ := (Fintype.prod_sum (κ := R) (R := ℂ)
      (fun i x => χ i x * sourcePrimeComponent S₀ P hP a ha n i x)).symm

theorem reflectionCRTGauss_cofactor
    (P : ι → HeightOneSpectrum (𝓞 K)) (hP : Pairwise fun i j => P i ≠ P j)
    (hS : ∀ i, P i ∉ principalizingSet S₀) (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (n : ι → ℕ)
    (χ : ∀ i, MulChar ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (n i)) ℂ) :
    (∑' x : (PrincipalIntegerRing S₀) ⧸ crtModulus S₀ P n,
      (∏ i, χ i (primeCRTEquiv S₀ P n hP x i)) *
        sourceCRTPhase S₀ P n (∏ i, a i ^ n i) (generatorProduct_ne_zero S₀ P a ha n)
          (crtModulus_generator S₀ P n a ha) x) =
      (∏ i, χ i (sourcePrimeCofactorUnit S₀ P hP a ha n i)) *
      ∏ i, ∑' x : (PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (n i),
        χ i x * sourcePrimePowerPhase S₀ (P i) (a i) (ha i) (n i) x := by
  rw [reflectionCRTGauss_factor S₀ P hP hS a ha n χ]
  let : ∀ i, Finite ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (n i)) :=
    fun i => primePowerQuotient_finite S₀ (P i) (hS i) (n i)
  let : ∀ i, Fintype ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (n i)) :=
    fun _ => Fintype.ofFinite _
  have hi (i : ι) :
      (∑' x : (PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (n i),
        χ i x * sourcePrimeComponent S₀ P hP a ha n i x) =
        χ i (sourcePrimeCofactorUnit S₀ P hP a ha n i) *
          ∑' x : (PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (n i),
            χ i x * sourcePrimePowerPhase S₀ (P i) (a i) (ha i) (n i) x := by
    rw [sourcePrimeComponent_eq_inverseShift]
    simp only [tsum_fintype]
    change gaussSum (χ i) ((sourcePrimePowerPhase S₀ (P i) (a i) (ha i) (n i)).mulShift
      ((sourcePrimeCofactorUnit S₀ P hP a ha n i)⁻¹ :
        ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (n i))ˣ)) = _
    rw [gaussSum_mulShift_eq]
    congr 1
    rw [MulChar.inv_apply, Ring.inverse_unit, inv_inv]
  simp_rw [hi]
  exact Finset.prod_mul_distrib

end
end ArtinMatthews.VaryingKummerAnalytic
