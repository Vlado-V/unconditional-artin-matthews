module

public import ArtinMatthews.CubicFrobeniusIntegral
public import ArtinMatthews.PowerResidues
public import Mathlib.RingTheory.Frobenius


set_option backward.privateInPublic true
@[expose] public section

/-! Reduction separates roots of an arbitrary prime-to-characteristic order,
and the genuine arithmetic Frobenius detects arbitrary power residues. -/

namespace ArtinMatthews

open scoped NumberField

/-- Reduction modulo an ideal is injective at the identity on roots of unity
whose order is invertible in the residue ring. -/
theorem power_unity_eq_one_of_reduction_eq_one
    {R : Type*} [CommRing R] [IsDomain R] (Q : Ideal R) {q : ℕ}
    (hq : (q : R) ∉ Q) {z : R} (hz : z ^ q = 1)
    (hred : Ideal.Quotient.mk Q z = 1) : z = 1 := by
  by_contra hne
  have hprod := geom_sum_mul z q
  rw [hz, sub_self] at hprod
  have hsum : ∑ i ∈ Finset.range q, z ^ i = 0 :=
    (mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hne)
  have hzero : (q : R ⧸ Q) = 0 := by
    simpa [hred] using congrArg (Ideal.Quotient.mk Q) hsum
  apply hq
  exact (Ideal.Quotient.eq_zero_iff_mem (I := Q)).mp (by simpa using hzero)

/-- A Frobenius-fixed root in a characteristic-p field is already a root
in the rational residue field. -/
theorem isPowerMod_of_frobenius_fixed {p q : ℕ} [Fact p.Prime]
    {F : Type*} [Field F] [CharP F p] {a : ℤ} {x : F}
    (hx : x ^ q = (a : F)) (hfix : x ^ p = x) :
    ∃ b : ZMod p, b ^ q = (a : ZMod p) := by
  have hbot : x ∈ (⊥ : Subfield F) := (Subfield.mem_bot_iff_pow_eq_self F p).mpr hfix
  obtain ⟨n, hn⟩ := (mem_bot_iff_intCast p F).mp hbot
  refine ⟨(n : ZMod p), ?_⟩
  let j : ZMod p →+* F := ZMod.castHom (m := p) dvd_rfl F
  apply j.injective
  have heq : (n : F) ^ q = (a : F) := by rw [hn, hx]
  simpa only [map_pow, map_intCast] using heq

/-- If q divides p−1, every qth root of a qth power from the prime field
is fixed by the p-power Frobenius. -/
theorem frobenius_fixed_of_isPowerMod {p q : ℕ} [Fact p.Prime]
    {F : Type*} [Field F] [CharP F p] {a : ℤ} {x : F}
    (hq : 0 < q) (hqd : q ∣ p - 1) (hx : x ^ q = (a : F))
    (ha : ∃ b : ZMod p, b ^ q = (a : ZMod p)) : x ^ p = x := by
  obtain ⟨b, hb⟩ := ha
  let j : ZMod p →+* F := ZMod.castHom (m := p) dvd_rfl F
  have hbF : (j b) ^ q = (a : F) := by
    have hh := congrArg j hb
    simpa only [map_pow, map_intCast] using hh
  by_cases hb0 : b = 0
  · have hx0 : x = 0 := by
      have hxq : x ^ q = 0 := by rw [hx, ← hbF, hb0, map_zero, zero_pow hq.ne']
      exact (pow_eq_zero_iff hq.ne').mp hxq
    rw [hx0, zero_pow (Fact.out : p.Prime).ne_zero]
  · have hbpow : (j b) ^ (p - 1) = 1 := by
      rw [← map_pow, ZMod.pow_card_sub_one_eq_one hb0, map_one]
    obtain ⟨k, hk⟩ := hqd
    have hp : p = q * k + 1 := by have := (Fact.out : p.Prime).pos; omega
    calc
      x ^ p = x ^ (q * k + 1) := congrArg (fun n : ℕ => x ^ n) hp
      _ = (x ^ q) ^ k * x := by rw [pow_add, pow_mul, pow_one]
      _ = (j b) ^ (p - 1) * x := by rw [hx, ← hbF, ← pow_mul, ← hk]
      _ = x := by rw [hbpow, one_mul]

section NumberField

variable {K : Type*} [Field K]

theorem powerRoot_isIntegral {q : ℕ} (hq : 0 < q) {a : ℤ} {x : K}
    (hx : x ^ q = (a : K)) : IsIntegral ℤ x := by
  apply IsIntegral.of_pow hq
  rw [hx]
  exact isIntegral_algebraMap

variable [NumberField K]
attribute [local instance] Ideal.Quotient.field

omit [NumberField K] in
/-- Integral qth roots of the same nonzero residue radicand are equal
if their reductions are equal, provided p does not divide q. -/
theorem powerRoot_eq_of_reduction_eq {q : ℕ} (hq : 0 < q)
    (Q : Ideal (𝓞 K)) [Q.IsMaximal] (hqQ : (q : 𝓞 K) ∉ Q)
    {a : ℤ} {x y : 𝓞 K} (hx : x ^ q = (a : 𝓞 K))
    (hy : y ^ q = (a : 𝓞 K)) (hyQ : Ideal.Quotient.mk Q y ≠ 0)
    (hred : Ideal.Quotient.mk Q x = Ideal.Quotient.mk Q y) : x = y := by
  have hy0 : (y : K) ≠ 0 := by
    intro hy0
    apply hyQ
    have hy' : y = 0 := Subtype.ext hy0
    rw [hy', map_zero]
  have haK : (a : K) ≠ 0 := by
    have hyK : (y : K) ^ q = (a : K) := congrArg (fun z : 𝓞 K => (z : K)) hy
    exact hyK ▸ pow_ne_zero q hy0
  let u : K := (x : K) / y
  have huq : u ^ q = 1 := by
    dsimp [u]
    rw [div_pow]
    have hxK : (x : K) ^ q = (a : K) := congrArg (fun z : 𝓞 K => (z : K)) hx
    have hyK : (y : K) ^ q = (a : K) := congrArg (fun z : 𝓞 K => (z : K)) hy
    rw [hxK, hyK, div_self haK]
  let z : 𝓞 K := ⟨u, powerRoot_isIntegral hq (a := 1) (by simpa using huq)⟩
  have hzq : z ^ q = 1 := by apply Subtype.ext; exact huq
  have hzmul : z * y = x := by apply Subtype.ext; exact div_mul_cancel₀ (x : K) hy0
  have hzred : Ideal.Quotient.mk Q z = 1 := by
    apply mul_right_cancel₀ hyQ
    rw [← map_mul, hzmul, hred, one_mul]
  have hzOne := power_unity_eq_one_of_reduction_eq_one Q hqQ hzq hzred
  have huOne : u = 1 := congrArg (fun z : 𝓞 K => (z : K)) hzOne
  apply Subtype.ext
  exact (div_eq_one_iff_eq hy0).mp huOne

/-- An actual arithmetic Frobenius fixes a qth root exactly when the
radicand is a qth power modulo p, if q divides p−1 and p does not divide a. -/
theorem arithFrob_fixes_powerRoot_iff {p q : ℕ} [Fact p.Prime]
    (hq : 0 < q) (hqd : q ∣ p - 1)
    (Q : Ideal (𝓞 K)) [Q.IsMaximal] [CharP ((𝓞 K) ⧸ Q) p]
    (hcard : Nat.card (ℤ ⧸ Q.under ℤ) = p)
    (σ : Gal(K/ℚ)) (hF : IsArithFrobAt ℤ σ Q)
    {a : ℤ} {x : K} (hx : x ^ q = (a : K)) (ha0 : (a : ZMod p) ≠ 0) :
    σ x = x ↔ ∃ b : ZMod p, b ^ q = (a : ZMod p) := by
  let r : 𝓞 K := ⟨x, powerRoot_isIntegral hq hx⟩
  have hr : r ^ q = (a : 𝓞 K) := by apply Subtype.ext; exact hx
  have hσr : (σ • r) ^ q = (a : 𝓞 K) := by
    apply Subtype.ext
    change (σ x) ^ q = (a : K)
    rw [← map_pow, hx, map_intCast]
  have hrcube : (Ideal.Quotient.mk Q r) ^ q = (a : (𝓞 K) ⧸ Q) := by
    rw [← map_pow, hr, map_intCast]
  have hσred : Ideal.Quotient.mk Q (σ • r) = (Ideal.Quotient.mk Q r) ^ p := by
    simpa only [hcard, MulSemiringAction.toAlgHom_apply] using hF.mk_apply r
  constructor
  · intro hfix
    have hrfix : σ • r = r := by apply Subtype.ext; exact hfix
    rw [hrfix] at hσred
    exact isPowerMod_of_frobenius_fixed hrcube hσred.symm
  · intro ha
    have hp : p.Prime := Fact.out
    have hqp : ¬ p ∣ q := by
      intro hpq
      have hp1 := hpq.trans hqd
      have hd := Nat.dvd_sub (dvd_refl p) hp1
      have he : p - (p - 1) = 1 := by have := hp.pos; omega
      rw [he] at hd
      exact hp.not_dvd_one hd
    have hqQ : (q : 𝓞 K) ∉ Q := by
      intro hmem
      have hzero : (q : (𝓞 K) ⧸ Q) = 0 := by
        simpa using (Ideal.Quotient.eq_zero_iff_mem (I := Q)).mpr hmem
      exact hqp ((CharP.cast_eq_zero_iff ((𝓞 K) ⧸ Q) p q).mp hzero)
    have haQ : (a : (𝓞 K) ⧸ Q) ≠ 0 := by
      intro hazero
      apply ha0
      let j : ZMod p →+* ((𝓞 K) ⧸ Q) := ZMod.castHom (m := p) dvd_rfl _
      apply j.injective
      simpa only [map_intCast, map_zero] using hazero
    have hr0 : Ideal.Quotient.mk Q r ≠ 0 := by
      intro hzero
      rw [hzero, zero_pow hq.ne'] at hrcube
      exact haQ hrcube.symm
    have hredfix := frobenius_fixed_of_isPowerMod hq hqd hrcube ha
    have hfix := powerRoot_eq_of_reduction_eq hq Q hqQ hσr hr hr0
      (hσred.trans hredfix)
    exact congrArg (fun z : 𝓞 K => (z : K)) hfix

end NumberField
end ArtinMatthews
