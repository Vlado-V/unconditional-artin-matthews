module

public import ArtinMatthews.SIntegerExteriorGenerator
public import ArtinMatthews.SIntegerCharacterTransport
public import ArtinMatthews.SIntegerPrincipalQuotient
public import ArtinMatthews.StandardAdelicGeneratorPhase
public import ArtinMatthews.StandardAdelicSIntegerPhase
public import ArtinMatthews.StandardAdelicSGeneratorComparison
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

/-! Full standard additive-phase transport on the actual S-integer
quotient. Integral representative coverage follows from localization;
the comparison with the coherent trace tower keeps its derived unit. -/
namespace ArtinMatthews.SIntegerQuotient

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.StandardAdelic ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]

def generatorFieldUnit (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a}) : Kˣ :=
  Units.mk0 (a : K) (fun h => exterior_generator_ne_zero S₀ P a ha (Subtype.ext h))

theorem generatorFieldUnit_val (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a}) :
    (generatorFieldUnit S₀ P a ha : K) = (a : K) := rfl

theorem generatorFieldUnit_valuation (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a}) :
    P.valuation K (generatorFieldUnit S₀ P a ha : K) = WithZero.exp (-1 : ℤ) :=
  exterior_generator_valuation S₀ P hP a ha

def standardGeneratorPhase (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (n : ℕ) : AddChar ((𝓞 K) ⧸ P.asIdeal ^ n) ℂ :=
  generatorPhase K P (generatorFieldUnit S₀ P a ha)
    (generatorFieldUnit_valuation S₀ P hP a ha) n

theorem standardGeneratorPhase_primitive (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (n : ℕ) (hbad : P ∉ traceBadPlaces K) :
    (standardGeneratorPhase S₀ P hP a ha n).IsPrimitive :=
  generatorPhase_primitive K P _ _ n hbad

theorem sIntegerQuotientPhase_eq_pull (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (n : ℕ) :
    sIntegerQuotientPhase K (principalizingSet S₀) (a ^ n)
        (pow_ne_zero n (exterior_generator_ne_zero S₀ P a ha)) =
      pullAddChar (generatorQuotientEquiv S₀ P hP a ha n)
        (standardGeneratorPhase S₀ P hP a ha n) := by
  let e := generatorQuotientEquiv S₀ P hP a ha n
  ext z
  obtain ⟨y, rfl⟩ := e.symm.surjective z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hm : e.symm (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (algebraMap (𝓞 K) (PrincipalIntegerRing S₀) x) :=
    generatorQuotientEquiv_symm_mk S₀ P hP a ha n x
  rw [hm, pullAddChar_apply, generatorQuotientEquiv_mk,
    sIntegerQuotientPhase_mk]
  change sCharacter K (principalizingSet S₀) ((x : K) / (a : K) ^ n) =
    generatorPhase K P (generatorFieldUnit S₀ P a ha)
      (generatorFieldUnit_valuation S₀ P hP a ha) n (Ideal.Quotient.mk _ x)
  rw [generatorPhase_mk]
  exact sCharacter_prime_power K (principalizingSet S₀) P hP
    (generatorFieldUnit S₀ P a ha)
    (fun Q hQ hQP => exterior_generator_other_valuation S₀ P a ha Q hQ hQP)
    n x (fun Q _ => Q.valuation_le_one x)

theorem sIntegerQuotientPhase_primitive (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (n : ℕ) (hbad : P ∉ traceBadPlaces K) :
    (sIntegerQuotientPhase K (principalizingSet S₀) (a ^ n)
      (pow_ne_zero n (exterior_generator_ne_zero S₀ P a ha))).IsPrimitive := by
  rw [sIntegerQuotientPhase_eq_pull S₀ P hP a ha n]
  exact pullAddChar_primitive _ _ (standardGeneratorPhase_primitive S₀ P hP a ha n hbad)

theorem sIntegerQuotientPhase_comparison_exists
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (n : ℕ) (hbad : P ∉ traceBadPlaces K) :
    ∃ b : ((𝓞 K) ⧸ P.asIdeal ^ n)ˣ,
      ∀ z : (PrincipalIntegerRing S₀) ⧸ Ideal.span {a ^ n},
        sIntegerQuotientPhase K (principalizingSet S₀) (a ^ n)
          (pow_ne_zero n (exterior_generator_ne_zero S₀ P a ha)) z =
        probeIdealPhase K P n ((b : _) * generatorQuotientEquiv S₀ P hP a ha n z) := by
  obtain ⟨b, hb⟩ := generatorPhase_comparison_exists K P (generatorFieldUnit S₀ P a ha)
    (generatorFieldUnit_valuation S₀ P hP a ha) n hbad
  refine ⟨b, ?_⟩
  intro z
  rw [sIntegerQuotientPhase_eq_pull S₀ P hP a ha n, pullAddChar_apply]
  exact (congrArg (fun ψ : AddChar ((𝓞 K) ⧸ P.asIdeal ^ n) ℂ =>
    ψ (generatorQuotientEquiv S₀ P hP a ha n z)) hb).symm

end
end ArtinMatthews.SIntegerQuotient
