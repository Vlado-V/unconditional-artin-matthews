module

public import ArtinMatthews.StandardAdelicSIntegerPhase
public import ArtinMatthews.StandardAdelicGeneratorPhase
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.RingTheory.Henselian
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

/-! Genuine global/local phase comparison at an exterior S-prime
generator. The integral-representative equality makes no assertion that
the two quotient rings have already been identified. -/
namespace ArtinMatthews.StandardAdelic

open NumberField IsDedekindDomain
open scoped NumberField BigOperators Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

theorem sCharacter_one_prime (S : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ S) (q : K)
    (hq : ∀ Q : HeightOneSpectrum (𝓞 K), Q ∉ S → Q ≠ P →
      algebraMap K (Q.adicCompletion K) q ∈ Q.adicCompletionIntegers K) :
    sCharacter K S q = localFiniteCharacter K P (-(algebraMap K (P.adicCompletion K) q)) := by
  rw [sCharacter_exterior_product, Finset.prod_eq_single P]
  · intro Q hQ hQP
    apply localFiniteCharacter_integral
    exact (Q.adicCompletionIntegers K).toSubring.neg_mem (hq Q (Finset.mem_sdiff.mp hQ).2 hQP)
  · intro hnot
    apply localFiniteCharacter_integral
    have hn : P ∉ rationalSupport K q := fun h => hnot (Finset.mem_sdiff.mpr ⟨h,hP⟩)
    have hi : algebraMap K (P.adicCompletion K) q ∈ P.adicCompletionIntegers K := by
      simpa only [mem_rationalSupport, not_not] using hn
    exact (P.adicCompletionIntegers K).toSubring.neg_mem hi

theorem sCharacter_prime_power (S : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ S) (p : Kˣ)
    (hp : ∀ Q : HeightOneSpectrum (𝓞 K), Q ∉ S → Q ≠ P → Q.valuation K (p : K) = 1)
    (n : ℕ) (x : K) (hx : ∀ Q : HeightOneSpectrum (𝓞 K), Q ∉ S → Q.valuation K x ≤ 1) :
    sCharacter K S (x/(p : K)^n) =
      localFiniteCharacter K P (-(algebraMap K (P.adicCompletion K) (x/(p : K)^n))) := by
  apply sCharacter_one_prime K S P hP
  intro Q hQS hQP
  change Valued.v ((x/(p : K)^n : K) : Q.adicCompletion K) ≤ 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_div₀, map_pow, hp Q hQS hQP, one_pow, div_one]
  exact hx Q hQS

theorem generatorPhase_eq_sCharacter (S : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ S) (p : Kˣ)
    (hprime : P.valuation K (p : K) = WithZero.exp (-1 : ℤ))
    (hp : ∀ Q : HeightOneSpectrum (𝓞 K), Q ∉ S → Q ≠ P → Q.valuation K (p : K) = 1)
    (n : ℕ) (x : 𝓞 K) :
    generatorPhase K P p hprime n (Ideal.Quotient.mk _ x) = sCharacter K S ((x : K)/(p : K)^n) := by
  rw [generatorPhase_mk]
  exact (sCharacter_prime_power K S P hP p hp n x (fun Q _ => Q.valuation_le_one x)).symm

def exteriorPrimeInteger (S : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (p : Kˣ)
    (hprime : P.valuation K (p : K) = WithZero.exp (-1 : ℤ))
    (hp : ∀ Q : HeightOneSpectrum (𝓞 K), Q ∉ S → Q ≠ P → Q.valuation K (p : K) = 1) :
    sIntegerRing K S := by
  refine ⟨p, ?_⟩
  intro Q hQ
  by_cases hQP : Q = P
  · subst Q
    rw [hprime, ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by norm_num)
  · rw [hp Q hQ hQP]

theorem exteriorPrimeInteger_ne_zero (S : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (p : Kˣ)
    (hprime : P.valuation K (p : K) = WithZero.exp (-1 : ℤ))
    (hp : ∀ Q : HeightOneSpectrum (𝓞 K), Q ∉ S → Q ≠ P → Q.valuation K (p : K) = 1) :
    exteriorPrimeInteger K S P p hprime hp ≠ 0 := by
  intro he
  exact p.ne_zero (congrArg (fun x : sIntegerRing K S => (x : K)) he)

theorem sIntegerQuotientPhase_eq_generator_on_integral (S : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ S) (p : Kˣ)
    (hprime : P.valuation K (p : K) = WithZero.exp (-1 : ℤ))
    (hp : ∀ Q : HeightOneSpectrum (𝓞 K), Q ∉ S → Q ≠ P → Q.valuation K (p : K) = 1)
    (n : ℕ) (x : 𝓞 K) :
    sIntegerQuotientPhase K S (exteriorPrimeInteger K S P p hprime hp ^ n)
        (pow_ne_zero n (exteriorPrimeInteger_ne_zero K S P p hprime hp))
        (Ideal.Quotient.mk _ (algebraMap (𝓞 K) (sIntegerRing K S) x)) =
      generatorPhase K P p hprime n (Ideal.Quotient.mk _ x) := by
  rw [sIntegerQuotientPhase_mk, generatorPhase_mk]
  change sCharacter K S ((x : K)/(p : K)^n) = _
  exact sCharacter_prime_power K S P hP p hp n x (fun Q _ => Q.valuation_le_one x)

end
end ArtinMatthews.StandardAdelic
