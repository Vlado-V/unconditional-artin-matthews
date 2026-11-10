module

public import ArtinMatthews.PrincipalHigherCancellation
public import ArtinMatthews.SIntegerHigherSourcePhase
public import ArtinMatthews.SIntegerLocalCOne
public import ArtinMatthews.SIntegerFiniteQuotients
public import ArtinMatthews.SIntegerHigherFourier
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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The literal higher outer-modulus source coefficient vanishes.
The congruence gate, quotient, two finite sums and primitive phase are
all actual S-integer constructions. -/
namespace ArtinMatthews.SIntegerFourier

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

def standardLocalHigher (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (m n J : ℕ) : ℂ :=
  ∑' d : (PrincipalIntegerRing S₀) ⧸ Ideal.span {a * a ^ m},
    if hd : a * a ^ m ∣ a ^ J - (a * a ^ n) * Quotient.out d then
      generatorResidueCharacter S₀ P hP a ha (χ ^ (m + 1)) (quotientReduction a (a ^ m) d) *
        sourceGaussAt S₀ P hP a ha (χ ^ (n + 1)) n
          (principalDivide (a * a ^ m) (a ^ J - (a * a ^ n) * Quotient.out d) hd)
    else 0

theorem standardLocalHigher_fourier (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hbad : P ∉ traceBadPlaces K)
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (m n J : ℕ) :
    (Nat.card (oppositeReduction (a * a ^ m) (a * a ^ n)).toAddMonoidHom.ker : ℂ) *
        standardLocalHigher S₀ P hP a ha χ m n J =
      principalHigherMixedSum a (a ^ m) (a * a ^ n)
        (sourceHigherPhase S₀ a (exterior_generator_ne_zero S₀ P a ha) m n)
        (generatorResidueCharacter S₀ P hP a ha (χ ^ (m + 1)))
        (generatorResidueCharacter S₀ P hP a ha (χ ^ (n + 1))) (a ^ J) := by
  have ha0 := exterior_generator_ne_zero S₀ P a ha
  let : Finite ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a * a ^ m}) :=
    principal_element_quotient_finite S₀ _ (mul_ne_zero ha0 (pow_ne_zero m ha0))
  let : Fintype ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a * a ^ m}) := Fintype.ofFinite _
  let : Finite ((PrincipalIntegerRing S₀) ⧸ Ideal.span {(a * a ^ m) * (a * a ^ n)}) :=
    principal_element_quotient_finite S₀ _
      (mul_ne_zero (mul_ne_zero ha0 (pow_ne_zero m ha0)) (mul_ne_zero ha0 (pow_ne_zero n ha0)))
  let : Fintype ((PrincipalIntegerRing S₀) ⧸ Ideal.span {(a * a ^ m) * (a * a ^ n)}) :=
    Fintype.ofFinite _
  calc
    _ = ∑' d : (PrincipalIntegerRing S₀) ⧸ Ideal.span {a * a ^ m},
        generatorResidueCharacter S₀ P hP a ha (χ ^ (m + 1)) (quotientReduction a (a ^ m) d) *
          sourceHigherGauss S₀ P hP a ha (χ ^ (n + 1)) m n
            (a ^ J - (a * a ^ n) * Quotient.out d) := by
      unfold standardLocalHigher
      rw [← tsum_mul_left]
      apply tsum_congr
      intro d
      rw [sourceHigherGauss_quotient S₀ P hP a ha hbad]
      by_cases hd : a * a ^ m ∣ a ^ J - (a * a ^ n) * Quotient.out d
      · simp only [dite_eq_left hd]
        ring
      · simp only [dite_eq_right hd, mul_zero]
    _ = _ := by
      unfold sourceHigherGauss oppositeFourier principalHigherMixedSum
      simp only [tsum_fintype, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro d _
      have hs : quotientScale (a * a ^ m) (a * a ^ n) d =
          Ideal.Quotient.mk _ ((a * a ^ n) * Quotient.out d) := by
        simpa only [Ideal.Quotient.mk_out] using
          quotientScale_mk (a * a ^ m) (a * a ^ n) (Quotient.out d)
      have hp : sourceHigherPhase S₀ a ha0 m n
          (Ideal.Quotient.mk _ (a ^ J - (a * a ^ n) * Quotient.out d) * v) =
          sourceHigherPhase S₀ a ha0 m n (Ideal.Quotient.mk _ (a ^ J) * v) *
            sourceHigherPhase S₀ a ha0 m n
              (-(quotientScale (a * a ^ m) (a * a ^ n) d * v)) := by
        rw [hs, map_sub, sub_mul, sub_eq_add_neg, AddChar.map_add_eq_mul]
      have hr : quotientReduction a (a ^ n)
          (oppositeReduction (a * a ^ m) (a * a ^ n) v) =
          quotientReduction a (a ^ m) (quotientReduction (a * a ^ m) (a * a ^ n) v) := by
        obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective v
        rfl
      rw [hp, hr]
      ring

theorem standardLocalHigher_eq_zero (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hbad : P ∉ traceBadPlaces K)
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (m n J : ℕ) (hm : 0 < m) :
    standardLocalHigher S₀ P hP a ha χ m n J = 0 := by
  have ha0 := exterior_generator_ne_zero S₀ P a ha
  let : Field ((𝓞 K) ⧸ P.asIdeal) := Ideal.Quotient.field _
  let : Finite ((PrincipalIntegerRing S₀) ⧸ Ideal.span {(a * a ^ m) * (a * a ^ n)}) :=
    principal_element_quotient_finite S₀ _
      (mul_ne_zero (mul_ne_zero ha0 (pow_ne_zero m ha0)) (mul_ne_zero ha0 (pow_ne_zero n ha0)))
  have hξ : generatorResidueCharacter S₀ P hP a ha (χ ^ (n + 1)) 0 = 0 := by
    change (χ ^ (n + 1)) (generatorResidueEquiv S₀ P hP a ha 0) = 0
    rw [map_zero, MulChar.map_zero]
  have hz := principalHigherMixedSum_eq_zero a (a ^ m) (a * a ^ n) ha0
    (mul_ne_zero ha0 (pow_ne_zero n ha0)) (dvd_pow_self a (Nat.ne_of_gt hm))
    (sourceHigherPhase S₀ a ha0 m n) (sourceHigherPhase_primitive S₀ P hP a ha hbad m n)
    (generatorResidueCharacter S₀ P hP a ha (χ ^ (m + 1)))
    (generatorResidueCharacter S₀ P hP a ha (χ ^ (n + 1))) hξ (a ^ J)
  have hk : (Nat.card (oppositeReduction (a * a ^ m) (a * a ^ n)).toAddMonoidHom.ker : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩ :
      Nat.card (oppositeReduction (a * a ^ m) (a * a ^ n)).toAddMonoidHom.ker ≠ 0)
  exact (mul_eq_zero.mp ((standardLocalHigher_fourier S₀ P hP a ha hbad χ m n J).trans hz)).resolve_left hk

end
end ArtinMatthews.SIntegerFourier
