module

public import ArtinMatthews.SIntegerSourceLocalCoefficient
public import ArtinMatthews.SourcePrincipalKernel
public import ArtinMatthews.SourcePrincipalAbsent
public import ArtinMatthews.SourcePrincipalCongruence
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

/-! A single literal finite local source kernel. Its degree generator
is explicitly equal to the corresponding prime power; no local value
table is built into this definition. -/
namespace ArtinMatthews.SourceCRTNormalization

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.SIntegerFourier
open scoped NumberField Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

def sourceDegreeGenerator (a : PrincipalIntegerRing S₀) : ℕ → PrincipalIntegerRing S₀
  | 0 => 1
  | n + 1 => a * a ^ n

theorem sourceDegreeGenerator_eq_pow (a : PrincipalIntegerRing S₀) (n : ℕ) :
    sourceDegreeGenerator S₀ a n = a ^ n := by
  cases n with
  | zero => simp only [sourceDegreeGenerator, pow_zero]
  | succ n => exact (pow_succ' a n).symm

theorem sourceDegreeGenerator_ne_zero (a : PrincipalIntegerRing S₀) (ha : a ≠ 0) (n : ℕ) :
    sourceDegreeGenerator S₀ a n ≠ 0 := by
  rw [sourceDegreeGenerator_eq_pow]
  exact pow_ne_zero n ha

def sourceDegreeWeight (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) :
    (n : ℕ) → ((PrincipalIntegerRing S₀) ⧸ Ideal.span {sourceDegreeGenerator S₀ a n}) → ℂ
  | 0, _ => 1
  | n + 1, x => generatorResidueCharacter S₀ P hP a ha (χ ^ (n + 1))
      (quotientReduction a (a ^ n) x)

def principalLocalCoefficient (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (t k J : ℕ) : ℂ :=
  principalSourceKernel S₀ (sourceDegreeGenerator S₀ a k) (sourceDegreeGenerator S₀ a t)
    (sourceDegreeGenerator_ne_zero S₀ a (exterior_generator_ne_zero S₀ P a ha) k)
    (sourceDegreeGenerator_ne_zero S₀ a (exterior_generator_ne_zero S₀ P a ha) t)
    (a ^ J) (sourceDegreeWeight S₀ P hP a ha χ k) (sourceDegreeWeight S₀ P hP a ha χ t)

theorem principalLocalCoefficient_positive (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (m n J : ℕ) :
    principalLocalCoefficient S₀ P hP a ha χ (n + 1) (m + 1) J =
      standardLocalHigher S₀ P hP a ha χ m n J := by
  unfold principalLocalCoefficient
  rw [principalSourceKernel_divide]
  rfl

theorem principalLocalCoefficient_zero_zero (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (J : ℕ) :
    principalLocalCoefficient S₀ P hP a ha χ 0 0 J = 1 :=
  principalSourceKernel_one_one S₀ (a ^ J)

theorem principalLocalCoefficient_zero_succ (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (k J : ℕ) :
    principalLocalCoefficient S₀ P hP a ha χ 0 (k + 1) J =
      standardLocalAbsent S₀ P hP a ha χ k J := by
  exact principalSourceKernel_inner_one S₀ (a * a ^ k)
    (mul_ne_zero (exterior_generator_ne_zero S₀ P a ha)
      (pow_ne_zero k (exterior_generator_ne_zero S₀ P a ha))) (a ^ J)
    (fun d => generatorResidueCharacter S₀ P hP a ha (χ ^ (k + 1)) (quotientReduction a (a ^ k) d))

theorem generatorResidueCharacter_pow (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ) :
    generatorResidueCharacter S₀ P hP a ha χ ^ n = generatorResidueCharacter S₀ P hP a ha (χ ^ n) :=
  (pullCharacter_pow (generatorResidueEquiv S₀ P hP a ha) χ n).symm

theorem principalLocalCoefficient_succ_zero (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n J : ℕ) :
    principalLocalCoefficient S₀ P hP a ha χ (n + 1) 0 J =
      standardLocalCZero S₀ P hP a ha χ n J := by
  have h := principalSourceKernel_outer_one S₀ (a * a ^ n)
    (mul_ne_zero (exterior_generator_ne_zero S₀ P a ha)
      (pow_ne_zero n (exterior_generator_ne_zero S₀ P a ha))) (a ^ J)
    (fun v => generatorResidueCharacter S₀ P hP a ha (χ ^ (n + 1)) (quotientReduction a (a ^ n) v))
  have he : (∑' v : (PrincipalIntegerRing S₀) ⧸ Ideal.span {a * a ^ n},
      generatorResidueCharacter S₀ P hP a ha (χ ^ (n + 1)) (quotientReduction a (a ^ n) v) *
        ArtinMatthews.StandardAdelic.sIntegerQuotientPhase K (principalizingSet S₀) (a * a ^ n)
          (mul_ne_zero (exterior_generator_ne_zero S₀ P a ha)
            (pow_ne_zero n (exterior_generator_ne_zero S₀ P a ha))) (Ideal.Quotient.mk _ (a ^ J) * v)) =
      standardLocalCZero S₀ P hP a ha χ n J := by
    unfold standardLocalCZero principalFourier
    rw [generatorResidueCharacter_pow]
    rfl
  exact h.trans he

theorem standardLocalHigher_zero (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n J : ℕ) :
    standardLocalHigher S₀ P hP a ha χ 0 n J = standardLocalCOne S₀ P hP a ha χ n J := by
  let B := a * a ^ n
  let W := fun d : (PrincipalIntegerRing S₀) ⧸ Ideal.span {a * a ^ 0} =>
    (generatorResidueCharacter S₀ P hP a ha (χ ^ 1)) (quotientReduction a (a ^ 0) d)
  let Z := fun v : (PrincipalIntegerRing S₀) ⧸ Ideal.span {B} =>
    generatorResidueCharacter S₀ P hP a ha (χ ^ (n + 1)) (quotientReduction a (a ^ n) v)
  have ha0 := exterior_generator_ne_zero S₀ P a ha
  have hB : B ≠ 0 := mul_ne_zero ha0 (pow_ne_zero n ha0)
  have hA : a * a ^ 0 ≠ 0 := mul_ne_zero ha0 (pow_ne_zero 0 ha0)
  have he : a * a ^ 0 = a := by rw [pow_zero, mul_one]
  have hleft : principalSourceKernel S₀ (a * a ^ 0) B hA hB (a ^ J) W Z =
      standardLocalHigher S₀ P hP a ha χ 0 n J := by
    rw [principalSourceKernel_divide]
    rfl
  have hright : principalSourceKernel S₀ a B ha0 hB (a ^ J)
      (generatorResidueCharacter S₀ P hP a ha χ) Z = standardLocalCOne S₀ P hP a ha χ n J := by
    rw [principalSourceKernel_divide]
    unfold standardLocalCOne
    rw [pow_succ']
    rfl
  have hc := principalSourceKernel_congr_left S₀ (a * a ^ 0) a B he hA ha0 hB (a ^ J) W Z
  have hw : (fun d => W ((Ideal.quotEquivOfEq
      (congrArg (fun x : PrincipalIntegerRing S₀ => Ideal.span {x}) he)).symm d)) =
      generatorResidueCharacter S₀ P hP a ha χ := by
    funext d
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective d
    rw [Ideal.quotEquivOfEq_symm, Ideal.quotEquivOfEq_mk]
    change generatorResidueCharacter S₀ P hP a ha (χ ^ 1) (Ideal.Quotient.mk _ x) = _
    rw [pow_one]
  rw [hw] at hc
  exact hleft.symm.trans (hc.trans hright)

theorem principalLocalCoefficient_eq_standard (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (t k J : ℕ) :
    principalLocalCoefficient S₀ P hP a ha χ t k J = standardLocalCoefficient S₀ P hP a ha χ t k J := by
  cases t with
  | zero =>
    cases k with
    | zero => exact principalLocalCoefficient_zero_zero S₀ P hP a ha χ J
    | succ k => exact principalLocalCoefficient_zero_succ S₀ P hP a ha χ k J
  | succ n =>
    cases k with
    | zero => exact principalLocalCoefficient_succ_zero S₀ P hP a ha χ n J
    | succ k =>
      rw [principalLocalCoefficient_positive]
      cases k with
      | zero => exact standardLocalHigher_zero S₀ P hP a ha χ n J
      | succ k => rfl

end
end ArtinMatthews.SourceCRTNormalization
