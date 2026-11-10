module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Data.Nat.ChineseRemainder
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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


set_option backward.privateInPublic true
@[expose] public section

/-!
# Local quadratic residue choices

For each prime larger than three, either quadratic sign can be imposed while
excluding the residues zero and one.  The positive sign is witnessed by four;
the negative sign uses the finite-field nonsquare existence theorem.
-/

namespace ArtinMatthews

/-- Each nonzero quadratic-character fiber contains exactly half of the
nonzero residues.  The cardinality identity is written without division. -/
theorem twice_card_quadratic_sign {q : ℕ} [Fact q.Prime]
    (hq : q ≠ 2) {s : ℤ} (hs : s = 1 ∨ s = -1) :
    2 * ((Finset.univ.filter fun u : ZMod q => quadraticChar (ZMod q) u = s).card : ℤ) =
      (q : ℤ) - 1 := by
  classical
  let χ := quadraticChar (ZMod q)
  let P := Finset.univ.filter fun u : ZMod q => χ u = 1
  let N := Finset.univ.filter fun u : ZMod q => χ u = -1
  have hchar : ringChar (ZMod q) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hq
  have hχsum : (∑ u : ZMod q, χ u) = 0 :=
    MulChar.sum_eq_zero_of_ne_one (quadraticChar_ne_one hchar)
  have hP : (∑ u : ZMod q, if χ u = 1 then (1 : ℤ) else 0) = P.card := by
    simp [P]
  have hN : (∑ u : ZMod q, if χ u = -1 then (1 : ℤ) else 0) = N.card := by
    simp [N]
  have hdiff : (P.card : ℤ) - N.card = 0 := by
    rw [← hP, ← hN, ← Finset.sum_sub_distrib]
    calc
      _ = ∑ u : ZMod q, χ u := by
        apply Finset.sum_congr rfl
        intro u _
        rcases quadraticChar_isQuadratic (ZMod q) u with h | h | h <;> simp [χ, h]
      _ = 0 := hχsum
  have htotal : (P.card : ℤ) + N.card + 1 = q := by
    rw [← hP, ← hN]
    have hpoint (u : ZMod q) :
        (if χ u = 1 then (1 : ℤ) else 0) +
          (if χ u = -1 then (1 : ℤ) else 0) + (if u = 0 then (1 : ℤ) else 0) = 1 := by
      by_cases hu : u = 0
      · simp [χ, hu]
      · rcases quadraticChar_dichotomy hu with h | h <;> simp [χ, hu, h]
    have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ)
      rfl (fun u _ => hpoint u)
    simpa [Finset.sum_add_distrib, ZMod.card] using hsum
  rcases hs with rfl | rfl
  · change 2 * (P.card : ℤ) = _
    omega
  · change 2 * (N.card : ℤ) = _
    omega

theorem zmod_two_ne_zero_of_prime_gt_three {q : ℕ} [Fact q.Prime] (hq : 3 < q) :
    (2 : ZMod q) ≠ 0 := by
  intro h
  have hd : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp h
  have := Nat.le_of_dvd (by norm_num : 0 < 2) hd
  omega

theorem zmod_four_ne_one_of_prime_gt_three {q : ℕ} [Fact q.Prime] (hq : 3 < q) :
    (2 : ZMod q) ^ 2 ≠ 1 := by
  intro h
  have hthree : (3 : ZMod q) = 0 := by linear_combination h
  have hd : q ∣ 3 := (ZMod.natCast_eq_zero_iff 3 q).mp hthree
  have := Nat.le_of_dvd (by norm_num : 0 < 3) hd
  omega

/-- Either Legendre sign has a representative different from both zero and
one at every prime greater than three. -/
theorem exists_quadratic_sign_avoiding_zero_one {q : ℕ} [Fact q.Prime]
    (hq : 3 < q) {s : ℤ} (hs : s = 1 ∨ s = -1) :
    ∃ u : ZMod q, u ≠ 0 ∧ u ≠ 1 ∧ quadraticChar (ZMod q) u = s := by
  rcases hs with rfl | rfl
  · have htwo := zmod_two_ne_zero_of_prime_gt_three hq
    exact ⟨(2 : ZMod q) ^ 2, pow_ne_zero _ htwo,
      zmod_four_ne_one_of_prime_gt_three hq, quadraticChar_sq_one' htwo⟩
  · have hchar : ringChar (ZMod q) ≠ 2 := by
      rw [ZMod.ringChar_zmod_n]
      omega
    obtain ⟨u, hu⟩ := quadraticChar_exists_neg_one (F := ZMod q) hchar
    refine ⟨u, ?_, ?_, hu⟩
    · intro hzero
      rw [hzero, quadraticChar_zero] at hu
      norm_num at hu
    · intro hone
      rw [hone, map_one] at hu
      norm_num at hu

/-- The same local choice as an ordinary least nonnegative integer residue. -/
theorem exists_legendre_residue_avoiding_zero_one {q : ℕ} [Fact q.Prime]
    (hq : 3 < q) {s : ℤ} (hs : s = 1 ∨ s = -1) :
    ∃ u : ℕ, u < q ∧ u ≠ 0 ∧ u ≠ 1 ∧ legendreSym q (u : ℤ) = s := by
  obtain ⟨u, hu0, hu1, hus⟩ := exists_quadratic_sign_avoiding_zero_one hq hs
  refine ⟨u.val, u.val_lt, ?_, ?_, ?_⟩
  · intro hzero
    apply hu0
    rw [← ZMod.natCast_zmod_val u, hzero, Nat.cast_zero]
  · intro hone
    apply hu1
    rw [← ZMod.natCast_zmod_val u, hone, Nat.cast_one]
  · simpa only [legendreSym, Int.cast_natCast, ZMod.natCast_zmod_val] using hus

/-- Arbitrary independently prescribed residues can be combined whenever
their positive moduli are pairwise coprime. -/
theorem exists_common_residue {ι : Type*} (t : Finset ι) (modulus residue : ι → ℕ)
    (hpositive : ∀ i ∈ t, modulus i ≠ 0)
    (hcoprime : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → (modulus i).Coprime (modulus j)) :
    ∃ u : ℕ, u < ∏ i ∈ t, modulus i ∧
      ∀ i ∈ t, u ≡ residue i [MOD modulus i] := by
  let u := Nat.chineseRemainderOfFinset residue modulus t hpositive hcoprime
  exact ⟨u, Nat.chineseRemainderOfFinset_lt_prod residue modulus hpositive hcoprime, u.property⟩

/-- The mod-eight choice and independently selected residues at distinct odd
primes combine into a single residue modulo their product. -/
theorem exists_common_residue_mod_eight (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ 2 < q) (residue : ℕ → ℕ) (r8 : ℕ) :
    ∃ u : ℕ, u < 8 * ∏ q ∈ Q, q ∧ u ≡ r8 [MOD 8] ∧
      ∀ q ∈ Q, u ≡ residue q [MOD q] := by
  classical
  have h8 : 8 ∉ Q := by
    intro hmem
    have h := (hQ 8 hmem).1
    norm_num at h
  have hcop8 : ∀ q ∈ Q, Nat.Coprime 8 q := by
    intro q hq
    have h := (hQ q hq).1.odd_of_ne_two (by have := (hQ q hq).2; omega)
    have hc : Nat.Coprime 2 q := h.coprime_two_left
    have hp := (Nat.coprime_pow_left_iff (by norm_num : 0 < 3) 2 q).mpr hc
    simpa using hp
  have hpositive : ∀ q ∈ insert 8 Q, (fun n : ℕ => n) q ≠ 0 := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · norm_num
    · exact (hQ q hq).1.ne_zero
  have hcoprime : ∀ q ∈ insert 8 Q, ∀ r ∈ insert 8 Q, q ≠ r → Nat.Coprime q r := by
    intro q hq r hr hqr
    rcases Finset.mem_insert.mp hq with rfl | hq
    · rcases Finset.mem_insert.mp hr with rfl | hr
      · exact (hqr rfl).elim
      · exact hcop8 r hr
    · rcases Finset.mem_insert.mp hr with rfl | hr
      · exact (hcop8 q hq).symm
      · exact (hQ q hq).1.coprime_iff_not_dvd.mpr
          (fun hd => hqr ((Nat.prime_dvd_prime_iff_eq (hQ q hq).1 (hQ r hr).1).mp hd))
  obtain ⟨u, hu, hures⟩ := exists_common_residue (insert 8 Q) (fun n => n)
    (fun q => if q = 8 then r8 else residue q) hpositive hcoprime
  refine ⟨u, ?_, ?_, ?_⟩
  · simpa only [Finset.prod_insert h8] using hu
  · simpa using hures 8 (Finset.mem_insert_self _ _)
  · intro q hq
    have hq8 : q ≠ 8 := by intro h; subst q; exact h8 hq
    simpa only [hq8, ↓reduceIte] using hures q (Finset.mem_insert_of_mem hq)

end ArtinMatthews
