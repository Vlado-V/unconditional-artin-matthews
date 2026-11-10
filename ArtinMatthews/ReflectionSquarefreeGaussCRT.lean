module

public import ArtinMatthews.SIntegerResidueGauss
public import ArtinMatthews.SourceCRTCofactorPhase
public import ArtinMatthews.ReflectionGaussCRT
public import ArtinMatthews.ReflectionGaussPrimeTransport
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

/-! The literal squarefree global quadratic Gauss sum, expanded through
the proved standard source CRT. Directed cross-prime characters remain
as actual cofactor evaluations. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField IsDedekindDomain SIntegerPrincipalization SIntegerQuotient
open SIntegerFourier StandardAdelic SourceCRTNormalization
open scoped NumberField Classical BigOperators
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem reflectionSquarefreeGauss_crt
    (P : ι → HeightOneSpectrum (𝓞 K)) (hP : Pairwise fun i j => P i ≠ P j)
    (hS : ∀ i, P i ∉ principalizingSet S₀) (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (χ : ∀ i, MulChar ((𝓞 K) ⧸ (P i).asIdeal) ℂ) :
    (∑' x : (PrincipalIntegerRing S₀) ⧸ Ideal.span {∏ i, a i ^ (1 : ℕ)},
      (sourceSexticWeight S₀ P hS a ha χ (fun _ => 1) (Quotient.out x)) ^ 2 *
        sIntegerQuotientPhase K (principalizingSet S₀) (∏ i, a i ^ (1 : ℕ))
          (generatorProduct_ne_zero S₀ P a ha (fun _ => 1)) x) =
      (∏ i, (generatorResidueCharacter S₀ (P i) (hS i) (a i) (ha i) (χ i)
        (Ideal.Quotient.mk _ (sourcePrimeCofactor S₀ a (fun _ => 1) i))) ^ 2) *
        ∏ i, residueSourceTau S₀ (P i) (hS i) (a i) (ha i) (χ i ^ 2) := by
  let n : ι → ℕ := fun _ => 1
  let E := Ideal.quotEquivOfEq (crtModulus_generator S₀ P n a ha)
  let C := fun i => reflectionLocalPrimeCharacter S₀ (P i) (hS i) (a i) (ha i) (χ i)
  have hchar (x : (PrincipalIntegerRing S₀) ⧸ crtModulus S₀ P n) :
      (sourceSexticWeight S₀ P hS a ha χ n (Quotient.out (E x))) ^ 2 =
        ∏ i, (C i ^ 2) (primeCRTEquiv S₀ P n hP x i) := by
    have hm : Ideal.Quotient.mk (crtModulus S₀ P n) (Quotient.out (E x)) = x := by
      apply E.injective
      rw [Ideal.quotEquivOfEq_mk, Ideal.Quotient.mk_out]
    have hw : sourceSexticWeight S₀ P hS a ha χ n (Quotient.out (E x)) =
        ∏ i, C i (primeCRTEquiv S₀ P n hP x i) := by
      unfold sourceSexticWeight crtResidueWeight
      apply Finset.prod_congr rfl
      intro i _
      change sourceLocalPowerWeight S₀ (P i) (hS i) (a i) (ha i) (χ i) 1
        (Ideal.Quotient.mk _ (Quotient.out (E x))) = C i (primeCRTEquiv S₀ P n hP x i)
      rw [← reflectionLocalPrimeCharacter_weight]
      congr 1
      rw [← primeCRTEquiv_mk S₀ P n hP, hm]
    rw [hw, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    exact (MulChar.pow_apply' (C i) (by decide : (2 : ℕ) ≠ 0) _).symm
  have he := E.toEquiv.tsum_eq (fun x =>
    (sourceSexticWeight S₀ P hS a ha χ n (Quotient.out x)) ^ 2 *
      sIntegerQuotientPhase K (principalizingSet S₀) (∏ i, a i ^ n i)
        (generatorProduct_ne_zero S₀ P a ha n) x)
  change _ = _ at he
  calc
    _ = ∑' x : (PrincipalIntegerRing S₀) ⧸ crtModulus S₀ P n,
        (∏ i, (C i ^ 2) (primeCRTEquiv S₀ P n hP x i)) *
          sourceCRTPhase S₀ P n (∏ i, a i ^ n i) (generatorProduct_ne_zero S₀ P a ha n)
            (crtModulus_generator S₀ P n a ha) x := by
      rw [← he]
      apply tsum_congr
      intro x
      change (sourceSexticWeight S₀ P hS a ha χ n (Quotient.out (E x))) ^ 2 *
        sIntegerQuotientPhase K (principalizingSet S₀) (∏ i, a i ^ n i)
          (generatorProduct_ne_zero S₀ P a ha n) (E x) = _
      rw [hchar]
      rfl
    _ = (∏ i, (C i ^ 2) (sourcePrimeCofactorUnit S₀ P hP a ha n i)) *
        ∏ i, ∑' x : (PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (n i),
          (C i ^ 2) x * sourcePrimePowerPhase S₀ (P i) (a i) (ha i) (n i) x :=
      reflectionCRTGauss_cofactor S₀ P hP hS a ha n (fun i => C i ^ 2)
    _ = _ := by
      congr 1
      · apply Finset.prod_congr rfl
        intro i _
        rw [MulChar.pow_apply_coe, sourcePrimeCofactorUnit_val]
        change (reflectionLocalPrimeCharacter S₀ (P i) (hS i) (a i) (ha i) (χ i)
          (Ideal.Quotient.mk _ _)) ^ 2 = _
        rw [reflectionLocalPrimeCharacter, pullCharacter_apply, reflectionLocalPrimeEquiv_mk]
        rfl
      · apply Finset.prod_congr rfl
        intro i _
        have hc : C i ^ 2 = reflectionLocalPrimeCharacter S₀ (P i) (hS i) (a i) (ha i) (χ i ^ 2) :=
          (pullCharacter_pow _ _ _).symm
        rw [hc]
        exact reflectionLocalPrimeGauss_eq S₀ (P i) (hS i) (a i) (ha i) (χ i ^ 2)

end
end ArtinMatthews.VaryingKummerAnalytic
