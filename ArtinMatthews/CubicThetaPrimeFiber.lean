module

public import ArtinMatthews.CubicReciprocityBridgeConjugation
public import ArtinMatthews.CubicThetaCoefficients
public import ArtinMatthews.CubicReciprocityBridgeRationalFrobenius
public import ArtinMatthews.CubicReciprocityBridgeRationalSymbol
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
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


set_option backward.privateInPublic true
@[expose] public section

/-! The two actual Eisenstein ideals of rational prime norm. -/

noncomputable section
open scoped NumberField BigOperators Pointwise
namespace ArtinMatthews
open OAI OAI.ActualEisensteinCubic
local notation "EO" => OAI.SevenEighths.HeckeFamily.O

theorem cubic_conjO_involutive : Function.Involutive conjO := by
  intro x
  apply ConcreteTraceCRT.eisEmbedding_injective
  simp only [eisEmbedding_conjO, star_star]

/-- Ideal conjugation in the orientation used by the actual Kummer field. -/
def conjugateEisensteinIdeal (P : Ideal EO) : Ideal EO := P.comap conjO

theorem conjugateEisensteinIdeal_absNorm (P : Ideal EO) :
    (conjugateEisensteinIdeal P).absNorm = P.absNorm := by
  let e := Ideal.quotientEquiv P (conjugateEisensteinIdeal P) conjO.symm
    (by simpa only [conjugateEisensteinIdeal, RingEquiv.symm_symm] using
      (Ideal.map_comap_of_equiv (I := P) conjO.symm).symm)
  exact (Nat.card_congr e.toEquiv).symm

/-- A prime-norm good ideal is not fixed by Eisenstein conjugation. -/
theorem conjugateEisensteinIdeal_ne {p : ℕ} (hp : p.Prime)
    (P : Ideal EO) [P.IsMaximal] (hP : P.absNorm = p) (hg : lambda ∉ P) :
    conjugateEisensteinIdeal P ≠ P := by
  classical
  let : Fintype (EO ⧸ P) := Fintype.ofFinite _
  have hcard : Fintype.card (EO ⧸ P) = p := by
    rw [← Nat.card_eq_fintype_card]
    exact hP
  let e := ZMod.ringEquivOfPrime (EO ⧸ P) hp hcard
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective (e.symm (Ideal.Quotient.mk P omega))
  have hred : Ideal.Quotient.mk P omega = (n : EO ⧸ P) := by
    have h := congrArg e hn
    simpa only [map_intCast, RingEquiv.apply_symm_apply] using h.symm
  have hmem : omega - (n : EO) ∈ P := by
    apply (Ideal.Quotient.eq_zero_iff_mem (I := P)).mp
    simp only [map_sub, map_intCast, hred, sub_self]
  intro heq
  have hconj : conjO (omega - (n : EO)) ∈ P := by
    change omega - (n : EO) ∈ conjugateEisensteinIdeal P
    rwa [heq]
  have hdiff : omega ^ 2 - omega ∈ P := by
    have h := P.sub_mem hconj hmem
    simpa only [map_sub, map_intCast, conjO_omega, sub_sub_sub_cancel_right] using h
  have hprod : omega * (omega - 1) ∈ P := by
    convert hdiff using 1; ring
  have hom : omega ∉ P := by
    intro h
    have h1 : (1 : EO) ∈ P := by
      have hcube : omega ^ 3 = 1 := omega_primitive.pow_eq_one
      rw [← hcube]
      exact P.pow_mem_of_mem h 3 (by decide)
    exact (inferInstance : P.IsPrime).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  exact hg (((inferInstance : P.IsPrime).mem_or_mem hprod).resolve_left hom)

/-- The actual prime and its conjugate multiply to the rational prime ideal. -/
theorem prime_mul_conjugateEisensteinIdeal {p : ℕ}
    (P : Ideal EO) [P.IsMaximal] (hP : P.absNorm = p) (hg : lambda ∉ P) :
    P * conjugateEisensteinIdeal P = Ideal.span {(p : EO)} := by
  obtain ⟨a, haP, haprim, _⟩ := cubicJacobi_exists_primary_generator P hg
  have hmul : a * conjO a = (p : EO) := by
    have h := primary_generator_mul_conj_eq_card P hg a haP haprim
    change a * conjO a = (P.absNorm : EO) at h
    rwa [hP] at h
  have hconj : conjugateEisensteinIdeal P = Ideal.span {conjO a} := by
    ext x
    change conjO x ∈ P ↔ x ∈ Ideal.span {conjO a}
    rw [haP, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    constructor
    · intro h
      have hh := map_dvd conjO h
      rwa [cubic_conjO_involutive x] at hh
    · intro h
      have hh := map_dvd conjO h
      rwa [cubic_conjO_involutive a] at hh
  rw [hconj, haP, Ideal.span_singleton_mul_span_singleton, hmul]

/-- There are exactly two Eisenstein ideals of prime norm at a good split prime. -/
theorem ideal_absNorm_prime_iff {p : ℕ} (hp : p.Prime)
    (P : Ideal EO) [P.IsMaximal] (hP : P.absNorm = p) (hg : lambda ∉ P)
    (I : Ideal EO) :
    I.absNorm = p ↔ I = P ∨ I = conjugateEisensteinIdeal P := by
  constructor
  · intro hI
    have hIr : Irreducible I.absNorm := by rw [hI]; exact (Nat.irreducible_iff_nat_prime p).mpr hp
    let : I.IsPrime := Ideal.isPrime_of_irreducible_absNorm hIr
    have hI0 : I ≠ ⊥ := by
      intro h
      have hz : I.absNorm = 0 := Ideal.absNorm_eq_zero_iff.mpr h
      exact hp.ne_zero (hI.symm.trans hz)
    let : I.IsMaximal := (inferInstance : I.IsPrime).isMaximal hI0
    have hprod : P * conjugateEisensteinIdeal P ≤ I := by
      rw [prime_mul_conjugateEisensteinIdeal P hP hg]
      rw [← hI]
      exact Ideal.span_singleton_absNorm_le I
    rcases (inferInstance : I.IsPrime).mul_le.mp hprod with h | h
    · exact Or.inl ((inferInstance : P.IsMaximal).eq_of_le
        (inferInstance : I.IsPrime).ne_top h).symm
    · have hQnorm : (conjugateEisensteinIdeal P).absNorm = p :=
        (conjugateEisensteinIdeal_absNorm P).trans hP
      have hQr : Irreducible (conjugateEisensteinIdeal P).absNorm := by
        rw [hQnorm]; exact (Nat.irreducible_iff_nat_prime p).mpr hp
      have hQprime := Ideal.isPrime_of_irreducible_absNorm hQr
      have hQ0 : conjugateEisensteinIdeal P ≠ ⊥ := by
        intro hz
        have hh : (conjugateEisensteinIdeal P).absNorm = 0 := Ideal.absNorm_eq_zero_iff.mpr hz
        exact hp.ne_zero (hQnorm.symm.trans hh)
      exact Or.inr ((hQprime.isMaximal hQ0).eq_of_le
        (inferInstance : I.IsPrime).ne_top h).symm
  · rintro (rfl | rfl)
    · exact hP
    · exact (conjugateEisensteinIdeal_absNorm P).trans hP

/-- The actual norm fiber, as a finite set, consists of those two distinct ideals. -/
theorem idealsOfNorm_prime {p : ℕ} (hp : p.Prime)
    (P : Ideal EO) [P.IsMaximal] (hP : P.absNorm = p) (hg : lambda ∉ P) :
    idealsOfNorm p = {P, conjugateEisensteinIdeal P} := by
  classical
  ext I
  simp only [mem_idealsOfNorm, ideal_absNorm_prime_iff hp P hP hg,
    Finset.mem_insert, Finset.mem_singleton]

/-- Natural theta coefficient at a rational split prime. -/
theorem idealThetaCoeff_prime {p : ℕ} (hp : p.Prime)
    (P : Ideal EO) [P.IsMaximal] (hP : P.absNorm = p) (hg : lambda ∉ P)
    (χ : OAI.SevenEighths.HeckeFamily.Character) :
    idealThetaCoeff χ p = thetaIdealCharacter χ P +
      thetaIdealCharacter χ (conjugateEisensteinIdeal P) := by
  classical
  rw [idealThetaCoeff, idealsOfNorm_prime hp P hP hg,
    Finset.sum_pair (Ne.symm (conjugateEisensteinIdeal_ne hp P hP hg))]

namespace IntegralFrobeniusData

variable {S : Finset ℤ} {p : ℕ} [Fact p.Prime]
  (D : IntegralFrobeniusData (integerCubicField S) p)

theorem eisensteinPrime_absNorm (hp3 : p % 3 = 1) : D.eisensteinPrime.absNorm = p :=
  D.eisenstein_residue_card hp3

omit [Fact p.Prime] in
theorem conjugate_eisensteinPrime :
    (D.conjugate (cubicKummerConjugation (integerCubicBases S))).eisensteinPrime =
      conjugateEisensteinIdeal D.eisensteinPrime := by
  change (cubicKummerConjugation (integerCubicBases S) • D.primeIdeal).under EO =
    (D.primeIdeal.under EO).comap conjO
  convert conjugate_prime_under_eisenstein S D.primeIdeal using 1
  ext a
  rfl

theorem idealThetaCoeff_split_prime (hp3 : p % 3 = 1)
    (χ : OAI.SevenEighths.HeckeFamily.Character) :
    idealThetaCoeff χ p = thetaIdealCharacter χ D.eisensteinPrime +
      thetaIdealCharacter χ
        (D.conjugate (cubicKummerConjugation (integerCubicBases S))).eisensteinPrime := by
  let : D.eisensteinPrime.IsMaximal := D.eisensteinPrime_maximal
  rw [D.conjugate_eisensteinPrime]
  exact idealThetaCoeff_prime (Fact.out : p.Prime) D.eisensteinPrime
    (D.eisensteinPrime_absNorm hp3) (D.eisensteinPrime_good hp3) χ

end IntegralFrobeniusData

end ArtinMatthews
