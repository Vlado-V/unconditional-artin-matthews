module

public import ArtinMatthews.SIntegerSexticReciprocity
public import ArtinMatthews.ProbeSexticCrossExponent
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

/-! The actual source cross-prime multipliers cancel for the constructed
allowed S-integer generators. Reciprocity is a proved input from the
preceding actual Hilbert/tame chain, not a supplied symbol law. -/
namespace ArtinMatthews.SIntegerTameSymbol

open NumberField IsDedekindDomain
open ArtinMatthews ArtinMatthews.AllowedGenerators ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.SIntegerResidueSymbol
open ArtinMatthews.SIntegerAllowedReciprocity ArtinMatthews.VaryingKummerAnalytic ArtinMatthews.AngularLambda
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K}

def sourceCrossUnit (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P Q : HeightOneSpectrum (𝓞 K)) (hPQ : P ≠ Q) (hP : P ∉ sourceHilbertSet K S₀)
    (a b : PrincipalIntegerRing (sourceHilbertSeed K S₀))
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing (sourceHilbertSeed K S₀))) = Ideal.span {a})
    (hb : Q.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing (sourceHilbertSeed K S₀))) = Ideal.span {b}) : ℂˣ :=
  (cyclotomicAngularResidueCharacter hζ P (sourcePrime_six_avoids K S₀ P hP)).toUnitHom
    (sIntegerResidueUnit K (sourceHilbertSeed K S₀) P hP a ha b
      (primeGenerator_other_avoids K (sourceHilbertSeed K S₀) P Q hPQ hP b hb))

theorem sourceCrossUnit_pow_six (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P Q : HeightOneSpectrum (𝓞 K)) (hPQ : P ≠ Q) (hP : P ∉ sourceHilbertSet K S₀)
    (a b : PrincipalIntegerRing (sourceHilbertSeed K S₀))
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing (sourceHilbertSeed K S₀))) = Ideal.span {a})
    (hb : Q.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing (sourceHilbertSeed K S₀))) = Ideal.span {b}) :
    sourceCrossUnit K hζ S₀ P Q hPQ hP a b ha hb ^ 6 = 1 := by
  apply Units.ext
  let χ := cyclotomicAngularResidueCharacter hζ P (sourcePrime_six_avoids K S₀ P hP)
  let u := sIntegerResidueUnit K (sourceHilbertSeed K S₀) P hP a ha b
    (primeGenerator_other_avoids K (sourceHilbertSeed K S₀) P Q hPQ hP b hb)
  have hp := pow_orderOf_eq_one χ
  rw [cyclotomicAngularResidueCharacter_order] at hp
  have hv := congrArg (fun θ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ => θ u) hp
  simpa only [sourceCrossUnit, χ, u, Units.val_pow_eq_pow_val, Units.val_one,
    MulChar.coe_toUnitHom, MulChar.pow_apply_coe, MulChar.one_apply_coe] using hv

theorem sourceCrossUnit_reciprocity (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P Q : HeightOneSpectrum (𝓞 K)) (hPQ : P ≠ Q)
    (hP : P ∉ sourceHilbertSet K S₀) (hQ : Q ∉ sourceHilbertSet K S₀)
    (a b : PrincipalIntegerRing (sourceHilbertSeed K S₀))
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing (sourceHilbertSeed K S₀))) = Ideal.span {a})
    (hb : Q.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing (sourceHilbertSeed K S₀))) = Ideal.span {b})
    (haB : generatorFieldUnit (sourceHilbertSeed K S₀) P a ha ∈ allowedSubgroup K hζ S₀)
    (hbB : generatorFieldUnit (sourceHilbertSeed K S₀) Q b hb ∈ allowedSubgroup K hζ S₀) :
    sourceCrossUnit K hζ S₀ P Q hPQ hP a b ha hb =
      sourceCrossUnit K hζ S₀ Q P hPQ.symm hQ b a hb ha := by
  apply Units.ext
  exact sourceAngularResidue_reciprocity K hζ S₀ P Q hPQ hP hQ a b ha hb haB hbB

theorem sourceCross_pair_cancel (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P Q : HeightOneSpectrum (𝓞 K)) (hPQ : P ≠ Q)
    (hP : P ∉ sourceHilbertSet K S₀) (hQ : Q ∉ sourceHilbertSet K S₀)
    (a b : PrincipalIntegerRing (sourceHilbertSeed K S₀))
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing (sourceHilbertSeed K S₀))) = Ideal.span {a})
    (hb : Q.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing (sourceHilbertSeed K S₀))) = Ideal.span {b})
    (haB : generatorFieldUnit (sourceHilbertSeed K S₀) P a ha ∈ allowedSubgroup K hζ S₀)
    (hbB : generatorFieldUnit (sourceHilbertSeed K S₀) Q b hb ∈ allowedSubgroup K hζ S₀)
    (e l e' l' k k' : ℤ) :
    let z := sourceCrossUnit K hζ S₀ P Q hPQ hP a b ha hb
    let z' := sourceCrossUnit K hζ S₀ Q P hPQ.symm hQ b a hb ha
    z ^ ((e+3*l)*k' + (e+3*l-k)*(e'+3*l')) *
      z' ^ ((e'+3*l')*k + (e'+3*l'-k')*(e+3*l)) * (z^2*z'^2) ^ (e*e') = 1 := by
  dsimp only
  rw [← sourceCrossUnit_reciprocity K hζ S₀ P Q hPQ hP hQ a b ha hb haB hbB]
  let z := sourceCrossUnit K hζ S₀ P Q hPQ hP a b ha hb
  change z ^ _ * z ^ _ * (z ^ (2 : ℕ) * z ^ (2 : ℕ)) ^ (e*e') = 1
  rw [← zpow_add, ← pow_add]
  have he : (e+3*l)*k' + (e+3*l-k)*(e'+3*l') +
      ((e'+3*l')*k + (e'+3*l'-k')*(e+3*l)) = 2*(e+3*l)*(e'+3*l') := by ring
  rw [he]
  change z ^ (2*(e+3*l)*(e'+3*l')) * (z ^ (4 : ℤ)) ^ (e*e') = 1
  rw [← zpow_mul]
  simpa only [mul_assoc] using
    probeCrossPair_zpow_eq_one z (sourceCrossUnit_pow_six K hζ S₀ P Q hPQ hP a b ha hb) e l e' l'

end
end ArtinMatthews.SIntegerTameSymbol
