module

public import ArtinMatthews.Definitions
public import Mathlib.RingTheory.Frobenius
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! Cubic residue witnesses and the actual prime-field Frobenius criterion. -/

namespace ArtinMatthews

open scoped NumberField

/-- Failure of obstruction (B), once its even square-class relation is
present, supplies a split cubic prime at which every base is a noncube. -/
theorem exists_noncube_prime_of_not_obstructionB {S : Finset ℤ}
    (hB : ¬ ObstructionB S)
    (hrel : ∃ T : Finset ℤ, T ⊆ S ∧ Even T.card ∧
      NegativeThreeRationalSquare (∏ a ∈ T, a)) :
    ∃ p : ℕ, p.Prime ∧ p % 3 = 1 ∧ ∀ a ∈ S, ¬ IsCubeMod p a := by
  classical
  have hcover : ¬ ∀ p : ℕ, p.Prime → p % 3 = 1 → ∃ a ∈ S, IsCubeMod p a :=
    fun h => hB ⟨hrel, h⟩
  push Not at hcover
  exact hcover

theorem noncube_mod_ne_zero {p : ℕ} {a : ℤ} (ha : ¬ IsCubeMod p a) :
    (a : ZMod p) ≠ 0 := by
  intro ha0
  apply ha
  exact ⟨0, by simp [ha0]⟩

/-- An element of a characteristic-`p` field fixed by `x ↦ x^p` belongs
to the prime field; a cubic root fixed by Frobenius therefore gives a cube
modulo `p`. -/
theorem isCubeMod_of_frobenius_fixed {p : ℕ} [Fact p.Prime]
    {F : Type*} [Field F] [CharP F p] {a : ℤ} {x : F}
    (hx : x ^ 3 = (a : F)) (hfix : x ^ p = x) : IsCubeMod p a := by
  have hbot : x ∈ (⊥ : Subfield F) := (Subfield.mem_bot_iff_pow_eq_self F p).mpr hfix
  obtain ⟨n, hn⟩ := (mem_bot_iff_intCast p F).mp hbot
  refine ⟨(n : ZMod p), ?_⟩
  let j : ZMod p →+* F := ZMod.castHom (m := p) dvd_rfl F
  apply j.injective
  have heq : (n : F) ^ 3 = (a : F) := by rw [hn, hx]
  simpa only [map_pow, map_intCast] using heq

/-- When `p ≡ 1 (mod 3)`, every cubic root of a cube from the prime field is
fixed by Frobenius. -/
theorem frobenius_fixed_of_isCubeMod {p : ℕ} [Fact p.Prime]
    {F : Type*} [Field F] [CharP F p] {a : ℤ} {x : F}
    (hp3 : p % 3 = 1) (hx : x ^ 3 = (a : F)) (ha : IsCubeMod p a) :
    x ^ p = x := by
  obtain ⟨b, hb⟩ := ha
  let j : ZMod p →+* F := ZMod.castHom (m := p) dvd_rfl F
  have hbF : (j b) ^ 3 = (a : F) := by
    have hh := congrArg j hb
    simpa only [map_pow, map_intCast] using hh
  by_cases hb0 : b = 0
  · have hx0 : x = 0 := by
      have hx3 : x ^ 3 = 0 := by rw [hx, ← hbF, hb0, map_zero, zero_pow (by decide)]
      exact (pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hx3
    rw [hx0, zero_pow (Fact.out : p.Prime).ne_zero]
  · have hbpow : (j b) ^ (p - 1) = 1 := by
      rw [← map_pow, ZMod.pow_card_sub_one_eq_one hb0, map_one]
    have hp : p = 3 * (p / 3) + 1 := by omega
    have hm : p - 1 = 3 * (p / 3) := by omega
    calc
      x ^ p = x ^ (3 * (p / 3) + 1) := congrArg (fun n : ℕ => x ^ n) hp
      _ = (x ^ 3) ^ (p / 3) * x := by rw [pow_add, pow_mul, pow_one]
      _ = (j b) ^ (p - 1) * x := by rw [hx, ← hbF, ← pow_mul, ← hm]
      _ = x := by rw [hbpow, one_mul]

/-- Actual Frobenius fixed points on cubic roots detect cubic residues. -/
theorem frobenius_fixed_iff_isCubeMod {p : ℕ} [Fact p.Prime]
    {F : Type*} [Field F] [CharP F p] {a : ℤ} {x : F}
    (hp3 : p % 3 = 1) (hx : x ^ 3 = (a : F)) :
    x ^ p = x ↔ IsCubeMod p a :=
  ⟨isCubeMod_of_frobenius_fixed hx, frobenius_fixed_of_isCubeMod hp3 hx⟩

/-- Reduction is injective on cubic roots of unity away from characteristic
three.  This is the separation needed to lift a fixed residue root. -/
theorem cube_unity_eq_one_of_reduction_eq_one {R : Type*} [CommRing R] [IsDomain R]
    (Q : Ideal R) (hthree : (3 : R) ∉ Q) {z : R} (hz : z ^ 3 = 1)
    (hred : Ideal.Quotient.mk Q z = 1) : z = 1 := by
  by_contra hne
  have hprod : (z - 1) * (z ^ 2 + z + 1) = 0 := by
    calc
      _ = z ^ 3 - 1 := by ring
      _ = 0 := by rw [hz, sub_self]
  have hsum : z ^ 2 + z + 1 = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hne)
  have hq := congrArg (Ideal.Quotient.mk Q) hsum
  have hzero : (3 : R ⧸ Q) = 0 := by
    simpa [hred, show (1 : R ⧸ Q) + 1 + 1 = 3 by norm_num] using hq
  exact hthree ((Ideal.Quotient.eq_zero_iff_mem (I := Q)).mp hzero)

section NumberFieldRoots

variable {K : Type*} [Field K]

theorem cubeRoot_isIntegral {a : ℤ} {x : K} (hx : x ^ 3 = (a : K)) :
    IsIntegral ℤ x := by
  apply IsIntegral.of_pow (by decide : 0 < 3)
  rw [hx]
  exact isIntegral_algebraMap

variable [NumberField K]

attribute [local instance] Ideal.Quotient.field

/-- A genuine arithmetic Frobenius cannot fix an integral cubic root if its
integer radicand is a noncube in the rational residue field. -/
theorem arithFrob_moves_cubeRoot {p : ℕ} [Fact p.Prime]
    (Q : Ideal (𝓞 K)) [Q.IsMaximal] [CharP ((𝓞 K) ⧸ Q) p]
    (hcard : Nat.card (ℤ ⧸ Q.under ℤ) = p)
    (σ : Gal(K/ℚ)) (hF : IsArithFrobAt ℤ σ Q)
    {a : ℤ} {x : K} (hx : x ^ 3 = (a : K)) (ha : ¬ IsCubeMod p a) :
    σ x ≠ x := by
  intro hfix
  let r : 𝓞 K := ⟨x, cubeRoot_isIntegral hx⟩
  have hrfix : σ • r = r := by
    apply Subtype.ext
    exact hfix
  have hredfix : (Ideal.Quotient.mk Q r) ^ p = Ideal.Quotient.mk Q r := by
    have h := hF.mk_apply r
    change Ideal.Quotient.mk Q (σ • r) =
      (Ideal.Quotient.mk Q r) ^ Nat.card (ℤ ⧸ Q.under ℤ) at h
    rw [hrfix, hcard] at h
    exact h.symm
  have hrcube : (Ideal.Quotient.mk Q r) ^ 3 = (a : (𝓞 K) ⧸ Q) := by
    rw [← map_pow]
    have hr : r ^ 3 = (a : 𝓞 K) := by
      apply Subtype.ext
      exact hx
    rw [hr, map_intCast]
  exact ha (isCubeMod_of_frobenius_fixed (F := (𝓞 K) ⧸ Q) hrcube hredfix)

/-- At a rational prime congruent to one modulo three, arithmetic Frobenius
fixes every cubic root of unity already present in the number field. -/
theorem arithFrob_fixes_cube_unity {p : ℕ} [Fact p.Prime]
    (Q : Ideal (𝓞 K)) [Q.IsMaximal] [CharP ((𝓞 K) ⧸ Q) p]
    (hcard : Nat.card (ℤ ⧸ Q.under ℤ) = p)
    (σ : Gal(K/ℚ)) (hF : IsArithFrobAt ℤ σ Q) (hp3 : p % 3 = 1)
    {ζ : K} (hζ : ζ ^ 3 = 1) : σ ζ = ζ := by
  have hp : p.Prime := Fact.out
  have hpne3 : p ≠ 3 := by intro h; rw [h] at hp3; norm_num at hp3
  let r : 𝓞 K := ⟨ζ, cubeRoot_isIntegral (a := 1) (by simpa using hζ)⟩
  have hr : r ^ 3 = 1 := by apply Subtype.ext; exact hζ
  have hthree : (3 : 𝓞 K) ∉ Q := by
    intro hmem
    have hzero : (3 : (𝓞 K) ⧸ Q) = 0 := by
      exact (Ideal.Quotient.eq_zero_iff_mem (I := Q)).mpr hmem
    have hd : p ∣ 3 := (CharP.cast_eq_zero_iff ((𝓞 K) ⧸ Q) p 3).mp hzero
    exact hpne3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd)
  have hf := hF.apply_of_pow_eq_one hr hthree
  rw [hcard] at hf
  have hpow : r ^ p = r := by
    calc
      r ^ p = r ^ (p % 3 + 3 * (p / 3)) := congrArg (fun n : ℕ => r ^ n) (Nat.mod_add_div p 3).symm
      _ = r := by rw [hp3, pow_add, pow_mul, hr, one_pow, mul_one, pow_one]
  have hfix : σ • r = r := hf.trans hpow
  exact congrArg (fun x : 𝓞 K => (x : K)) hfix

/-- Away from the radicand and from three, a cubic residue makes the genuine
arithmetic Frobenius fix every cubic root in the number field. -/
theorem arithFrob_fixes_cubeRoot_of_isCubeMod {p : ℕ} [Fact p.Prime]
    (Q : Ideal (𝓞 K)) [Q.IsMaximal] [CharP ((𝓞 K) ⧸ Q) p]
    (hcard : Nat.card (ℤ ⧸ Q.under ℤ) = p)
    (σ : Gal(K/ℚ)) (hF : IsArithFrobAt ℤ σ Q) (hp3 : p % 3 = 1)
    {a : ℤ} {x : K} (hx : x ^ 3 = (a : K))
    (ha0 : (a : ZMod p) ≠ 0) (ha : IsCubeMod p a) : σ x = x := by
  have haInt : a ≠ 0 := by intro h; simp [h] at ha0
  have haK : (a : K) ≠ 0 := by exact_mod_cast haInt
  have hx0 : x ≠ 0 := by intro h; rw [h, zero_pow (by decide)] at hx; exact haK hx.symm
  let r : 𝓞 K := ⟨x, cubeRoot_isIntegral hx⟩
  have hrcube : (Ideal.Quotient.mk Q r) ^ 3 = (a : (𝓞 K) ⧸ Q) := by
    rw [← map_pow]
    have hr : r ^ 3 = (a : 𝓞 K) := by apply Subtype.ext; exact hx
    rw [hr, map_intCast]
  have haQ : (a : (𝓞 K) ⧸ Q) ≠ 0 := by
    intro hazero
    apply ha0
    let j : ZMod p →+* ((𝓞 K) ⧸ Q) := ZMod.castHom (m := p) dvd_rfl _
    apply j.injective
    simpa only [map_intCast, map_zero] using hazero
  have hr0 : Ideal.Quotient.mk Q r ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (by decide)] at hrcube
    exact haQ hrcube.symm
  have hredfix : (Ideal.Quotient.mk Q r) ^ p = Ideal.Quotient.mk Q r :=
    frobenius_fixed_of_isCubeMod hp3 hrcube ha
  have hσred : Ideal.Quotient.mk Q (σ • r) = Ideal.Quotient.mk Q r := by
    have h := hF.mk_apply r
    change Ideal.Quotient.mk Q (σ • r) =
      (Ideal.Quotient.mk Q r) ^ Nat.card (ℤ ⧸ Q.under ℤ) at h
    rw [hcard, hredfix] at h
    exact h
  let u : K := σ x / x
  have hu3 : u ^ 3 = 1 := by
    dsimp [u]
    rw [div_pow, ← map_pow, hx, map_intCast, div_self haK]
  let z : 𝓞 K := ⟨u, cubeRoot_isIntegral (a := 1) (by simpa using hu3)⟩
  have hz3 : z ^ 3 = 1 := by apply Subtype.ext; exact hu3
  have hzmul : z * r = σ • r := by
    apply Subtype.ext
    exact div_mul_cancel₀ (σ x) hx0
  have hzred : Ideal.Quotient.mk Q z = 1 := by
    apply mul_right_cancel₀ hr0
    rw [← map_mul, hzmul, hσred, one_mul]
  have hthree : (3 : 𝓞 K) ∉ Q := by
    intro hmem
    have hzero : (3 : (𝓞 K) ⧸ Q) = 0 := (Ideal.Quotient.eq_zero_iff_mem (I := Q)).mpr hmem
    have hd : p ∣ 3 := (CharP.cast_eq_zero_iff ((𝓞 K) ⧸ Q) p 3).mp hzero
    have hp : p.Prime := Fact.out
    have heq := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd
    rw [heq] at hp3
    norm_num at hp3
  have hzOne := cube_unity_eq_one_of_reduction_eq_one Q hthree hz3 hzred
  apply (div_eq_one_iff_eq hx0).mp
  exact congrArg (fun t : 𝓞 K => (t : K)) hzOne

/-- The complete characteristic-zero Frobenius/cubic-residue equivalence. -/
theorem arithFrob_fixes_cubeRoot_iff {p : ℕ} [Fact p.Prime]
    (Q : Ideal (𝓞 K)) [Q.IsMaximal] [CharP ((𝓞 K) ⧸ Q) p]
    (hcard : Nat.card (ℤ ⧸ Q.under ℤ) = p)
    (σ : Gal(K/ℚ)) (hF : IsArithFrobAt ℤ σ Q) (hp3 : p % 3 = 1)
    {a : ℤ} {x : K} (hx : x ^ 3 = (a : K)) (ha0 : (a : ZMod p) ≠ 0) :
    σ x = x ↔ IsCubeMod p a := by
  constructor
  · intro hfix
    by_contra hno
    exact arithFrob_moves_cubeRoot Q hcard σ hF hx hno hfix
  · exact arithFrob_fixes_cubeRoot_of_isCubeMod Q hcard σ hF hp3 hx ha0

end NumberFieldRoots

end ArtinMatthews
