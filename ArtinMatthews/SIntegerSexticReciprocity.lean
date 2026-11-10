module

public import ArtinMatthews.EisensteinAngularCyclotomic
public import ArtinMatthews.ProbeAngularResidueSymbol
public import ArtinMatthews.SIntegerAllowedHilbertPair
public import ArtinMatthews.SIntegerPowerResidueSymbol
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import ArtinMatthews.SIntegerAngularResidueSymbol
public import ArtinMatthews.SIntegerTameGlobalComparison
public import ClassFieldTheory.KummerTheory.Concrete.CyclotomicPrimeBaseChange
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! Genuine sextic reciprocity for the constructed allowed S-integer
prime generators. The actual paper/CFT transpose, exterior valuations,
local tame formula and finite residue transport are all discharged. -/
namespace ArtinMatthews.SIntegerTameSymbol

open NumberField IsDedekindDomain KummerTheory
open GlobalClassFieldTheory.Reciprocity AlgebraicNumberTheory.PowerResidueSymbols
open ArtinMatthews ArtinMatthews.AllowedGenerators ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.SIntegerResidueSymbol
open ArtinMatthews.SIntegerAllowedReciprocity ArtinMatthews.VaryingKummerAnalytic ArtinMatthews.AngularLambda
open OAI OAI.ActualEisensteinCubic OAI.ConcreteTraceCRT
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

theorem sourcePrime_six_avoids (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ sourceHilbertSet K S₀) :
    (6 : 𝓞 K) ∉ P.asIdeal := by
  apply (P.valuation_eq_one_iff_notMem (K := K)).mp
  exact sourceSix_unit_valuation K S₀ P hP

theorem primeGenerator_other_avoids (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P Q : HeightOneSpectrum (𝓞 K)) (hPQ : P ≠ Q) (hP : P ∉ principalizingSet S₀)
    (b : PrincipalIntegerRing S₀)
    (hb : Q.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {b}) :
    b ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) := by
  intro hm
  have hv := exterior_generator_other_valuation S₀ Q b hb P hP hPQ
  have hl := (principalInteger_power_mem_iff_valuation S₀ P hP 1 b).mp (by simpa only [pow_one] using hm)
  rw [hv] at hl
  have ht : WithZero.exp (-1 : ℤ) < (1 : WithZero (Multiplicative ℤ)) := by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by norm_num)
  exact (not_le_of_gt ht) hl

theorem sourcePairResidueSymbols_equal {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P Q : HeightOneSpectrum (𝓞 K)) (hPQ : P ≠ Q)
    (hP : P ∉ sourceHilbertSet K S₀) (hQ : Q ∉ sourceHilbertSet K S₀)
    (a b : PrincipalIntegerRing (sourceHilbertSeed K S₀))
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing (sourceHilbertSeed K S₀))) = Ideal.span {a})
    (hb : Q.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing (sourceHilbertSeed K S₀))) = Ideal.span {b})
    (haB : generatorFieldUnit (sourceHilbertSeed K S₀) P a ha ∈ allowedSubgroup K hζ S₀)
    (hbB : generatorFieldUnit (sourceHilbertSeed K S₀) Q b hb ∈ allowedSubgroup K hζ S₀) :
    sIntegerPowerResidueSymbol K (sourceHilbertSeed K S₀) P hP a ha probeSix (sourceSixRoots K hζ)
        (probePrimeNorm_coprime_six K P (sourcePrime_six_avoids K S₀ P hP)) b
        (primeGenerator_other_avoids K (sourceHilbertSeed K S₀) P Q hPQ hP b hb) =
      sIntegerPowerResidueSymbol K (sourceHilbertSeed K S₀) Q hQ b hb probeSix (sourceSixRoots K hζ)
        (probePrimeNorm_coprime_six K Q (sourcePrime_six_avoids K S₀ Q hQ)) a
        (primeGenerator_other_avoids K (sourceHilbertSeed K S₀) Q P hPQ.symm hQ a ha) := by
  have hr := sourceAllowedPrime_pair_reciprocity K hζ S₀ P Q hPQ hP hQ a b ha hb haB hbB
  have hp := sourceGlobalHilbert_unit_generator K (sourceHilbertSeed K S₀) P hP a ha
      (sourcePrime_six_avoids K S₀ P hP) (sourceSixRoots K hζ) b
      (primeGenerator_other_avoids K (sourceHilbertSeed K S₀) P Q hPQ hP b hb)
      (generatorFieldUnit (sourceHilbertSeed K S₀) Q b hb) rfl
  have hq := sourceGlobalHilbert_unit_generator K (sourceHilbertSeed K S₀) Q hQ b hb
      (sourcePrime_six_avoids K S₀ Q hQ) (sourceSixRoots K hζ) a
      (primeGenerator_other_avoids K (sourceHilbertSeed K S₀) Q P hPQ.symm hQ a ha)
      (generatorFieldUnit (sourceHilbertSeed K S₀) P a ha) rfl
  exact integralRootsOfUnityToNthRoots_injective K 6 (hp.symm.trans (hr.trans hq))

theorem sourceAngularResidue_reciprocity {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P Q : HeightOneSpectrum (𝓞 K)) (hPQ : P ≠ Q)
    (hP : P ∉ sourceHilbertSet K S₀) (hQ : Q ∉ sourceHilbertSet K S₀)
    (a b : PrincipalIntegerRing (sourceHilbertSeed K S₀))
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing (sourceHilbertSeed K S₀))) = Ideal.span {a})
    (hb : Q.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing (sourceHilbertSeed K S₀))) = Ideal.span {b})
    (haB : generatorFieldUnit (sourceHilbertSeed K S₀) P a ha ∈ allowedSubgroup K hζ S₀)
    (hbB : generatorFieldUnit (sourceHilbertSeed K S₀) Q b hb ∈ allowedSubgroup K hζ S₀) :
    cyclotomicAngularResidueCharacter hζ P (sourcePrime_six_avoids K S₀ P hP)
        (generatorResidueEquiv (sourceHilbertSeed K S₀) P hP a ha (Ideal.Quotient.mk _ b)) =
      cyclotomicAngularResidueCharacter hζ Q (sourcePrime_six_avoids K S₀ Q hQ)
        (generatorResidueEquiv (sourceHilbertSeed K S₀) Q hQ b hb (Ideal.Quotient.mk _ a)) := by
  let : Algebra BaseField K := baseAlgebraOfTwelve hζ
  have hs := sourcePairResidueSymbols_equal K hζ S₀ P Q hPQ hP hQ a b ha hb haB hbB
  have hp := sIntegerAngularRoot_eq_symbol K (sourceHilbertSeed K S₀) P hP a ha
    (sourcePrime_six_avoids K S₀ P hP) (sourceSixRoots K hζ) b
    (primeGenerator_other_avoids K (sourceHilbertSeed K S₀) P Q hPQ hP b hb)
  have hq := sIntegerAngularRoot_eq_symbol K (sourceHilbertSeed K S₀) Q hQ b hb
    (sourcePrime_six_avoids K S₀ Q hQ) (sourceSixRoots K hζ) a
    (primeGenerator_other_avoids K (sourceHilbertSeed K S₀) Q P hPQ.symm hQ a ha)
  have he := hp.trans (hs.trans hq.symm)
  have hv := congrArg (fun z : rootsOfUnity 6 (𝓞 K) => ((z.1 : (𝓞 K)ˣ) : 𝓞 K)) he
  simp only [probeIntegralSixthRoot_val] at hv
  have hi := (FaithfulSMul.algebraMap_injective BaseIntegers (𝓞 K)) hv
  change globalAngularResidueCharacter K P _ _ = globalAngularResidueCharacter K Q _ _
  rw [probeAngularIntegralCharacter_complex, probeAngularIntegralCharacter_complex]
  exact congrArg eisEmbedding hi

end
end ArtinMatthews.SIntegerTameSymbol
