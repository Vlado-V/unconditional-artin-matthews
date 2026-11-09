module

public import ArtinMatthews.QuadraticResidueChoice
public import ArtinMatthews.ProgressionDensityProduct
public import ArtinMatthews.EnlargedProgressionCountingCore
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.Algebra.Group.Pi.Units


set_option backward.privateInPublic true
@[expose] public section

/-! The finite Chinese-remainder count underlying equation (10.4). -/

namespace ArtinMatthews

def enlargedModulus (M₀ : ℕ) (P : Finset ℕ) : ℕ := M₀ * ∏ q ∈ P, q

def enlargedModulusFamily (M₀ : ℕ) (P : Finset ℕ) : Option {q // q ∈ P} → ℕ
  | none => M₀
  | some q => q.val

theorem enlargedModulusFamily_prod (M₀ : ℕ) (P : Finset ℕ) :
    (∏ i, enlargedModulusFamily M₀ P i) = enlargedModulus M₀ P := by
  classical
  simp only [Fintype.prod_option, enlargedModulusFamily, enlargedModulus]
  exact congrArg (M₀ * ·) (Finset.prod_coe_sort P (fun q : ℕ => q))

theorem enlargedModulusFamily_ne_zero {M₀ : ℕ} (hM₀ : M₀ ≠ 0) {P : Finset ℕ}
    (hP : ∀ q ∈ P, q.Prime ∧ 3 < q ∧ ¬ q ∣ M₀) (i : Option {q // q ∈ P}) :
    enlargedModulusFamily M₀ P i ≠ 0 := by
  cases i with
  | none => exact hM₀
  | some q => exact (hP q.val q.property).1.ne_zero

theorem enlargedModulusFamily_pairwise {M₀ : ℕ} {P : Finset ℕ}
    (hP : ∀ q ∈ P, q.Prime ∧ 3 < q ∧ ¬ q ∣ M₀) :
    Pairwise fun i j => Nat.Coprime (enlargedModulusFamily M₀ P i)
      (enlargedModulusFamily M₀ P j) := by
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some q => exact ((hP q.val q.property).1.coprime_iff_not_dvd.mpr
        (hP q.val q.property).2.2).symm
  | some q =>
    cases j with
    | none => exact (hP q.val q.property).1.coprime_iff_not_dvd.mpr ((hP q.val q.property).2.2)
    | some r =>
      apply (hP q.val q.property).1.coprime_iff_not_dvd.mpr
      intro hd
      have heq := (Nat.prime_dvd_prime_iff_eq (hP q.val q.property).1
        (hP r.val r.property).1).mp hd
      exact hij (congrArg some (Subtype.ext heq))

/-- The base coordinate is fixed and each new prime coordinate avoids one;
zero is already excluded because every coordinate is a unit. -/
noncomputable def enlargedAllowedUnits {M₀ : ℕ} {P : Finset ℕ}
    (hP : ∀ q ∈ P, q.Prime ∧ 3 < q ∧ ¬ q ∣ M₀) (u₀ : (ZMod M₀)ˣ) :
    (i : Option {q // q ∈ P}) → Finset (ZMod (enlargedModulusFamily M₀ P i))ˣ
  | none => {u₀}
  | some q => by
    let : NeZero q.val := ⟨(hP q.val q.property).1.ne_zero⟩
    change Finset (ZMod q.val)ˣ
    exact Finset.univ.erase 1

theorem enlargedAllowedUnits_card_none {M₀ : ℕ} {P : Finset ℕ}
    (hP : ∀ q ∈ P, q.Prime ∧ 3 < q ∧ ¬ q ∣ M₀) (u₀ : (ZMod M₀)ˣ) :
    (enlargedAllowedUnits hP u₀ none).card = 1 := by
  classical
  change ({u₀} : Finset (ZMod M₀)ˣ).card = 1
  exact Finset.card_singleton u₀

theorem enlargedAllowedUnits_card_some {M₀ : ℕ} {P : Finset ℕ}
    (hP : ∀ q ∈ P, q.Prime ∧ 3 < q ∧ ¬ q ∣ M₀) (u₀ : (ZMod M₀)ˣ)
    (q : {q // q ∈ P}) : (enlargedAllowedUnits hP u₀ (some q)).card = q.val - 2 := by
  classical
  let : NeZero q.val := ⟨(hP q.val q.property).1.ne_zero⟩
  change (Finset.univ.erase (1 : (ZMod q.val)ˣ)).card = q.val - 2
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    ZMod.card_units_eq_totient, Nat.totient_prime (hP q.val q.property).1]
  omega

theorem enlargedAllowedUnits_card_prod {M₀ : ℕ} {P : Finset ℕ}
    (hP : ∀ q ∈ P, q.Prime ∧ 3 < q ∧ ¬ q ∣ M₀) (u₀ : (ZMod M₀)ˣ) :
    (∏ i, (enlargedAllowedUnits hP u₀ i).card) = ∏ q ∈ P, (q - 2) := by
  classical
  rw [Fintype.prod_option, enlargedAllowedUnits_card_none, one_mul]
  simp_rw [enlargedAllowedUnits_card_some]
  exact Finset.prod_coe_sort P (fun q => q - 2)

/-- The actual finite set of allowed unit residue classes modulo the enlarged
modulus.  Its defining CRT restrictions fix the old class and remove one at
each new prime. -/
noncomputable def enlargedProgressionUnits {M₀ : ℕ} {P : Finset ℕ}
    [NeZero (enlargedModulus M₀ P)]
    (hP : ∀ q ∈ P, q.Prime ∧ 3 < q ∧ ¬ q ∣ M₀) (u₀ : (ZMod M₀)ˣ) :
    Finset (ZMod (enlargedModulus M₀ P))ˣ :=
  allowedUnitClasses (enlargedModulusFamily M₀ P) (enlargedModulusFamily_pairwise hP)
    (enlargedModulusFamily_prod M₀ P).symm (enlargedAllowedUnits hP u₀)

theorem enlargedProgressionUnits_card {M₀ : ℕ} {P : Finset ℕ}
    [NeZero (enlargedModulus M₀ P)]
    (hP : ∀ q ∈ P, q.Prime ∧ 3 < q ∧ ¬ q ∣ M₀) (u₀ : (ZMod M₀)ˣ) :
    (enlargedProgressionUnits hP u₀).card = ∏ q ∈ P, (q - 2) := by
  rw [enlargedProgressionUnits, card_allowedUnitClasses]
  exact enlargedAllowedUnits_card_prod hP u₀

/-- The CRT definition is exactly the stated congruence condition on actual
unit classes.  A unit coordinate is automatically nonzero. -/
theorem mem_enlargedProgressionUnits_iff {M₀ : ℕ} {P : Finset ℕ}
    [NeZero (enlargedModulus M₀ P)]
    (hP : ∀ q ∈ P, q.Prime ∧ 3 < q ∧ ¬ q ∣ M₀) (u₀ : (ZMod M₀)ˣ)
    (u : (ZMod (enlargedModulus M₀ P))ˣ) :
    u ∈ enlargedProgressionUnits hP u₀ ↔
      Units.map (ZMod.castHom (dvd_mul_right M₀ (∏ q ∈ P, q)) (ZMod M₀)).toMonoidHom u = u₀ ∧
      ∀ q (hq : q ∈ P),
        Units.map (ZMod.castHom ((Finset.dvd_prod_of_mem (fun q : ℕ => q) hq).trans
          (dvd_mul_left (∏ q ∈ P, q) M₀)) (ZMod q)).toMonoidHom u ≠ 1 := by
  classical
  rw [enlargedProgressionUnits, mem_allowedUnitClasses]
  constructor
  · intro h
    constructor
    · have hh := h none
      change crtUnitsEquivOfEq (enlargedModulusFamily M₀ P)
        (enlargedModulusFamily_pairwise hP) (enlargedModulusFamily_prod M₀ P).symm u none ∈
          ({u₀} : Finset (ZMod M₀)ˣ) at hh
      have heq := Finset.mem_singleton.mp hh
      rw [crtUnitsEquivOfEq_apply] at heq
      exact heq
    · intro q hq
      let : NeZero q := ⟨(hP q hq).1.ne_zero⟩
      have hh := h (some ⟨q, hq⟩)
      change crtUnitsEquivOfEq (enlargedModulusFamily M₀ P)
        (enlargedModulusFamily_pairwise hP) (enlargedModulusFamily_prod M₀ P).symm u
          (some (⟨q, hq⟩ : {q // q ∈ P})) ∈ (Finset.univ : Finset (ZMod q)ˣ).erase 1 at hh
      have hn := (Finset.mem_erase.mp hh).1
      rw [crtUnitsEquivOfEq_apply] at hn
      exact hn
  · rintro ⟨hbase, hnew⟩ i
    cases i with
    | none =>
      change crtUnitsEquivOfEq (enlargedModulusFamily M₀ P)
        (enlargedModulusFamily_pairwise hP) (enlargedModulusFamily_prod M₀ P).symm u none ∈
          ({u₀} : Finset (ZMod M₀)ˣ)
      apply Finset.mem_singleton.mpr
      rw [crtUnitsEquivOfEq_apply]
      exact hbase
    | some q =>
      let : NeZero q.val := ⟨(hP q.val q.property).1.ne_zero⟩
      let : Fintype (ZMod (enlargedModulusFamily M₀ P (some q)))ˣ :=
        inferInstanceAs (Fintype (ZMod q.val)ˣ)
      change crtUnitsEquivOfEq (enlargedModulusFamily M₀ P)
        (enlargedModulusFamily_pairwise hP) (enlargedModulusFamily_prod M₀ P).symm u (some q) ∈
          (Finset.univ : Finset (ZMod q.val)ˣ).erase 1
      apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_univ _⟩
      rw [crtUnitsEquivOfEq_apply]
      exact hnew q.val q.property

theorem totient_prod_distinct_primes (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) :
    Nat.totient (∏ q ∈ P, q) = ∏ q ∈ P, (q - 1) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert q P hq ih =>
    have hqprime := hP q (Finset.mem_insert_self _ _)
    have hprest : ∀ r ∈ P, r.Prime := fun r hr => hP r (Finset.mem_insert_of_mem hr)
    have hcop : Nat.Coprime q (∏ r ∈ P, r) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro r hr
      apply hqprime.coprime_iff_not_dvd.mpr
      intro hd
      have heq := (Nat.prime_dvd_prime_iff_eq hqprime (hprest r hr)).mp hd
      exact hq (heq ▸ hr)
    rw [Finset.prod_insert hq, Nat.totient_mul hcop, Nat.totient_prime hqprime,
      ih hprest, Finset.prod_insert hq]

theorem enlargedModulus_totient {M₀ : ℕ} {P : Finset ℕ}
    (hP : ∀ q ∈ P, q.Prime ∧ 3 < q ∧ ¬ q ∣ M₀) :
    Nat.totient (enlargedModulus M₀ P) = Nat.totient M₀ * ∏ q ∈ P, (q - 1) := by
  have hcop : Nat.Coprime M₀ (∏ q ∈ P, q) := by
    apply Nat.coprime_prod_right_iff.mpr
    intro q hq
    exact ((hP q hq).1.coprime_iff_not_dvd.mpr (hP q hq).2.2).symm
  rw [enlargedModulus, Nat.totient_mul hcop,
    totient_prod_distinct_primes P (fun q hq => (hP q hq).1)]

/-- Equation (10.4), with its numerator proved to be the cardinality of the
actual finite set of admissible unit classes. -/
theorem enlargedProgressionUnits_density {M₀ : ℕ} {P : Finset ℕ}
    [NeZero (enlargedModulus M₀ P)]
    (hP : ∀ q ∈ P, q.Prime ∧ 3 < q ∧ ¬ q ∣ M₀) (u₀ : (ZMod M₀)ˣ) :
    ((enlargedProgressionUnits hP u₀).card : ℝ) /
        Nat.totient (enlargedModulus M₀ P) =
      (1 / (Nat.totient M₀ : ℝ)) * progressionDensityProduct P := by
  rw [enlargedProgressionUnits_card, enlargedModulus_totient hP, Nat.cast_mul,
    Nat.cast_prod, Nat.cast_prod]
  have hnum : (∏ q ∈ P, ((q - 2 : ℕ) : ℝ)) = ∏ q ∈ P, ((q : ℝ) - 2) := by
    apply Finset.prod_congr rfl
    intro q hq
    rw [Nat.cast_sub (show 2 ≤ q by have := (hP q hq).2.1; omega)]
    norm_num
  have hden : (∏ q ∈ P, ((q - 1 : ℕ) : ℝ)) = ∏ q ∈ P, ((q : ℝ) - 1) := by
    apply Finset.prod_congr rfl
    intro q hq
    rw [Nat.cast_sub (show 1 ≤ q by have := (hP q hq).2.1; omega)]
    norm_num
  rw [hnum, hden, progressionDensityProduct, Finset.prod_div_distrib]
  ring

end ArtinMatthews
