module

public import ArtinMatthews.ArtinAbelianLocalFactors
public import Mathlib.RingTheory.WittVector.IsPoly
public import OAI.NumberTheory.PrimePackets.IdealCoefficients
public import ArtinMatthews.VaryingKummerAnalyticDedekindNonvanishingLocal
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Exact regrouping of actual prime ideals in a number-field tower. -/
noncomputable section
namespace ArtinMatthews.AbelianLocal
open OAI.PrimeDegreePackets ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField IsMulCommutative Classical BigOperators
open UniqueFactorizationMonoid

lemma mem_idealsOverPrime_iff (K : Type*) [Field K] [NumberField K]
    {p : ℕ} (hp : p ≠ 0) (P : Ideal (𝓞 K)) :
    P ∈ idealsOverPrime K p ↔ P.IsPrime ∧ (p : 𝓞 K) ∈ P := by
  have hspan : (Ideal.span {(p : 𝓞 K)}) ≠ ⊥ := by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] using hp
  rw [idealsOverPrime, Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hspan,
    Ideal.span_singleton_le_iff_mem]

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E]

 

def primeIdealTowerEquiv (p : ℕ) (hp : p ≠ 0) :
    (Σ P : idealsOverPrime F p, Ideal.primesOver P.val (𝓞 E)) ≃ idealsOverPrime E p := by
  let f : (Σ P : idealsOverPrime F p, Ideal.primesOver P.val (𝓞 E)) →
      idealsOverPrime E p := fun IQ => by
    refine ⟨IQ.2.val, (mem_idealsOverPrime_iff E hp _).mpr ⟨IQ.2.property.1, ?_⟩⟩
    have hP := ((mem_idealsOverPrime_iff F hp _).mp IQ.1.property).2
    rw [IQ.2.property.2.over] at hP
    simpa only [Ideal.mem_under, map_natCast] using hP
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨P, Q⟩ ⟨P', Q'⟩ he
    have hQ : Q.val = Q'.val := congrArg Subtype.val he
    have hP : P = P' := Subtype.ext (by
      rw [Q.property.2.over, Q'.property.2.over, hQ])
    cases hP
    exact congrArg (Sigma.mk P) (Subtype.ext hQ)
  · intro Q
    have hQ := (mem_idealsOverPrime_iff E hp _).mp Q.property
    let : Q.val.IsPrime := hQ.1
    have hP : Q.val.under (𝓞 F) ∈ idealsOverPrime F p := by
      apply (mem_idealsOverPrime_iff F hp _).mpr
      refine ⟨inferInstance, ?_⟩
      simpa only [Ideal.mem_under, map_natCast] using hQ.2
    refine ⟨⟨⟨Q.val.under (𝓞 F), hP⟩, ⟨Q.val, hQ.1, inferInstance⟩⟩, ?_⟩
    rfl

lemma primeIdealTowerEquiv_val (p : ℕ) (hp : p ≠ 0)
    (PQ : Σ P : idealsOverPrime F p, Ideal.primesOver P.val (𝓞 E)) :
    (primeIdealTowerEquiv F E p hp PQ).val = PQ.2.val := rfl

 

/-- The height-one prime associated to an actual prime over p. -/
def primeOverHeightOne (K : Type*) [Field K] [NumberField K]
    (p : Nat.Primes) (P : idealsOverPrime K p) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
  ⟨P.val, ((mem_idealsOverPrime_iff K p.property.ne_zero P.val).mp P.property).1,
    (idealsOverPrime_prime K P.property).ne_zero⟩

variable [IsAbelianGalois F E]

/-- All local Artin factors above a rational prime, for one global character. -/
def abelianArtinRationalFactor (χ : Gal(E/F) →* ℂˣ) (p : Nat.Primes) (s : ℂ) : ℂ :=
  ∏ P : idealsOverPrime F p, abelianArtinLocalFactor F E χ (primeOverHeightOne F p P) s

local instance rationalCharacterFintype : Fintype (Gal(E/F) →* ℂˣ) := Fintype.ofFinite _

/-- Regrouping the exact all-ramification local factorization over a rational prime. -/
theorem prod_abelianArtinRationalFactor (p : Nat.Primes) (s : ℂ) :
    (∏ χ : Gal(E/F) →* ℂˣ, abelianArtinRationalFactor F E χ p s) =
      ∏ Q : idealsOverPrime E p, (1 - (Ideal.absNorm Q.val : ℂ) ^ (-s))⁻¹ := by
  let (P : idealsOverPrime F p) : Fintype (Ideal.primesOver P.val (𝓞 E)) := by
    let : P.val.IsPrime :=
      ((mem_idealsOverPrime_iff F p.property.ne_zero P.val).mp P.property).1
    exact (Algebra.QuasiFinite.finite_primesOver P.val).fintype
  unfold abelianArtinRationalFactor
  rw [Finset.prod_comm]
  simp_rw [prod_abelianArtinLocalFactor]
  rw [← (primeIdealTowerEquiv F E p p.property.ne_zero).prod_comp]
  simp only [primeIdealTowerEquiv_val, Fintype.prod_sigma, primeOverHeightOne]
  congr 1

end ArtinMatthews.AbelianLocal
