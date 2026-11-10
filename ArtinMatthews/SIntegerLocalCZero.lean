module

public import ArtinMatthews.PrincipalQuotientFourier
public import ArtinMatthews.SIntegerExteriorGenerator
public import ArtinMatthews.SIntegerSexticTransport
public import ArtinMatthews.StandardAdelicLocalNontrivial
public import ArtinMatthews.StandardAdelicSIntegerPhase
public import ArtinMatthews.SIntegerFiniteQuotients
public import ArtinMatthews.SIntegerPhaseCongruence
public import ArtinMatthews.SIntegerStandardPhase
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The literal zero-outer-degree local source coefficient in an actual
S-integer prime generator. Its support and exact residue lifting are
derived in the standard source phase, not imported from a chosen trace
tower. -/
namespace ArtinMatthews.SIntegerFourier

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

def linearPowerPhase (a : PrincipalIntegerRing S₀) (ha : a ≠ 0) (n : ℕ) :
    AddChar ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a * a ^ n}) ℂ :=
  sIntegerQuotientPhase K (principalizingSet S₀) (a * a ^ n) (mul_ne_zero ha (pow_ne_zero n ha))

theorem linearPowerPhase_primitive (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (n : ℕ) (hbad : P ∉ traceBadPlaces K) :
    (linearPowerPhase S₀ a (exterior_generator_ne_zero S₀ P a ha) n).IsPrimitive := by
  unfold linearPowerPhase
  exact (sourcePhase_primitive_congr S₀ _ _ _ _ (pow_succ' a n).symm).mpr
    (sIntegerQuotientPhase_primitive S₀ P hP a ha (n + 1) hbad)

theorem linearPowerPhase_lower (a : PrincipalIntegerRing S₀) (ha : a ≠ 0) (n : ℕ) :
    quotientLowerChar a (a ^ n) (linearPowerPhase S₀ a ha n) =
      sIntegerQuotientPhase K (principalizingSet S₀) a ha := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [quotientLowerChar_mk]
  change sIntegerQuotientPhase K (principalizingSet S₀) (a * a ^ n) _
    (Ideal.Quotient.mk _ (a ^ n * x)) = _
  rw [sIntegerQuotientPhase_mk, sIntegerQuotientPhase_mk]
  have haK : (a : K) ≠ 0 := fun h => ha (Subtype.ext h)
  congr 1
  change ((a : K)^n * (x : K)) / ((a : K) * (a : K)^n) = (x : K) / (a : K)
  field_simp

theorem generator_power_mem_iff (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a}) (n J : ℕ) :
    a ^ J ∈ (P.asIdeal ^ n).map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) ↔ n ≤ J := by
  rw [principalInteger_power_mem_iff_valuation S₀ P hP n]
  have hv : P.valuation K ((a ^ J : PrincipalIntegerRing S₀) : K) = WithZero.exp (-(J : ℤ)) := by
    change P.valuation K ((a : K) ^ J) = _
    rw [map_pow, exterior_generator_valuation S₀ P hP a ha, ← WithZero.exp_nsmul]
    congr 1
    simp
  rw [hv, WithZero.exp_le_exp]
  omega

def standardLocalCZero (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n J : ℕ) : ℂ :=
  principalFourier a (a ^ n) (linearPowerPhase S₀ a (exterior_generator_ne_zero S₀ P a ha) n)
    (fun z => (generatorResidueCharacter S₀ P hP a ha χ ^ (n + 1)) z) (a ^ J)

theorem standardLocalCZero_support (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hbad : P ∉ traceBadPlaces K) (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n J : ℕ)
    (hn : standardLocalCZero S₀ P hP a ha χ n J ≠ 0) : n ≤ J := by
  apply (generator_power_mem_iff S₀ P hP a ha n J).mp
  rw [generator_power_ideal S₀ P a ha n, Ideal.mem_span_singleton]
  exact principalFourier_support a (a ^ n) (exterior_generator_ne_zero S₀ P a ha) _
    (linearPowerPhase_primitive S₀ P hP a ha n hbad) _ _ hn

theorem standardLocalCZero_zero_off_support (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hbad : P ∉ traceBadPlaces K) (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n J : ℕ) (hJn : J < n) :
    standardLocalCZero S₀ P hP a ha χ n J = 0 := by
  by_contra hn
  exact Nat.not_le_of_gt hJn (standardLocalCZero_support S₀ P hP a ha hbad χ n J hn)

theorem linearReduction_kernel_card (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a}) (n : ℕ) :
    Nat.card (quotientReduction a (a ^ n)).toAddMonoidHom.ker = Ideal.absNorm P.asIdeal ^ n := by
  have hc := AddSubgroup.card_ker_mul_card_of_surjective
    (f := (quotientReduction a (a ^ n)).toAddMonoidHom) (quotientReduction_surjective a (a ^ n))
  have hl : Nat.card ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a}) = Ideal.absNorm P.asIdeal := by
    simpa only [pow_one] using generatorQuotient_card S₀ P hP a ha 1
  have hu : Nat.card ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a * a ^ n}) =
      Ideal.absNorm P.asIdeal ^ (n + 1) := by
    rw [← pow_succ']
    exact generatorQuotient_card S₀ P hP a ha (n + 1)
  rw [hl, hu, pow_succ] at hc
  exact Nat.eq_of_mul_eq_mul_right
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot)) hc

theorem standardLocalCZero_lift (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n J : ℕ) (hnJ : n ≤ J) :
    standardLocalCZero S₀ P hP a ha χ n J =
      (Ideal.absNorm P.asIdeal : ℂ) ^ n *
        ∑' z : (PrincipalIntegerRing S₀) ⧸ Ideal.span {a},
          (generatorResidueCharacter S₀ P hP a ha χ ^ (n + 1)) z *
            sIntegerQuotientPhase K (principalizingSet S₀) a
              (exterior_generator_ne_zero S₀ P a ha) (Ideal.Quotient.mk _ (a ^ (J - n)) * z) := by
  let : Finite ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a}) :=
    principal_element_quotient_finite S₀ a (exterior_generator_ne_zero S₀ P a ha)
  let : Finite ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a * a ^ n}) :=
    principal_element_quotient_finite S₀ _ (mul_ne_zero (exterior_generator_ne_zero S₀ P a ha)
      (pow_ne_zero n (exterior_generator_ne_zero S₀ P a ha)))
  have he : a ^ J = a ^ n * a ^ (J - n) := by rw [← pow_add, Nat.add_sub_of_le hnJ]
  unfold standardLocalCZero
  rw [he, principalFourier_lift, linearPowerPhase_lower,
    linearReduction_kernel_card S₀ P hP a ha n, Nat.cast_pow]

end
end ArtinMatthews.SIntegerFourier
