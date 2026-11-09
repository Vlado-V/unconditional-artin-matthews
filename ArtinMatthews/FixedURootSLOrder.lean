module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-!
# The squarefree fixed-u special-linear group order

The finite-field special-linear cardinality and the literal CRT ring
equivalence yield the real order formula used in PD (det:SL-order).
-/

namespace ArtinMatthews

open scoped BigOperators

/-- Entrywise transport along a ring equivalence preserves determinant one. -/
def specialLinearRingEquiv {n R S : Type*} [Fintype n] [DecidableEq n]
    [CommRing R] [CommRing S] (e : R ≃+* S) :
    Matrix.SpecialLinearGroup n R ≃ Matrix.SpecialLinearGroup n S where
  toFun := Matrix.SpecialLinearGroup.map e.toRingHom
  invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  left_inv A := by ext i j; exact e.symm_apply_apply (A i j)
  right_inv A := by ext i j; exact e.apply_symm_apply (A i j)

set_option backward.isDefEq.respectTransparency false in
/-- Determinant-one matrices over a product ring are tuples of determinant-one matrices. -/
def specialLinearPiEquiv {n ι : Type*} [Fintype n] [DecidableEq n]
    (R : ι → Type*) [∀ i, CommRing (R i)] :
    Matrix.SpecialLinearGroup n (∀ i, R i) ≃ (∀ i, Matrix.SpecialLinearGroup n (R i)) where
  toFun A i := Matrix.SpecialLinearGroup.map (Pi.evalRingHom R i) A
  invFun B := ⟨fun r c i => B i r c, by
    funext i
    change (Pi.evalRingHom R i) (Matrix.det (fun r c i => B i r c)) = 1
    rw [RingHom.map_det]
    exact (B i).prop⟩
  left_inv A := by ext r c i; rfl
  right_inv B := by funext i; ext r c; rfl

/-- The natural-number finite-field order, before passing to its real Euler-factor form. -/
theorem finite_field_card_SL_two {K : Type*} [Field K] [Fintype K] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) =
      Fintype.card K * ((Fintype.card K) ^ 2 - 1) := by
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have h := Matrix.card_SL_field (𝔽 := K) 2
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one] at h
  have hdiff : (Fintype.card K) ^ 2 - Fintype.card K =
      Fintype.card K * (Fintype.card K - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one, pow_two]
  rw [hdiff, ← mul_assoc, Nat.mul_div_cancel _ (Nat.sub_pos_of_lt hq)] at h
  simpa only [mul_comm] using h

/-- Exact finite-field order as a real expression without natural fractions. -/
theorem finite_field_card_SL_two_real {K : Type*} [Field K] [Fintype K] :
    (Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) : ℝ) =
      (Fintype.card K : ℝ) ^ 3 * (1 - 1 / (Fintype.card K : ℝ) ^ 2) := by
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hq0 : (Fintype.card K : ℝ) ≠ 0 := by exact_mod_cast (by omega : Fintype.card K ≠ 0)
  have hq2 : 1 ≤ (Fintype.card K) ^ 2 := by nlinarith
  rw [finite_field_card_SL_two, Nat.cast_mul, Nat.cast_sub hq2, Nat.cast_pow, Nat.cast_one]
  field_simp

/-- CRT of a squarefree modulus into the residue fields at its prime factors. -/
noncomputable def squarefreeZModPrimeEquiv {S : ℕ} (hS : Squarefree S) :
    ZMod S ≃+* (∀ p : S.primeFactors, ZMod (p : ℕ)) := by
  have hprod : (∏ p : S.primeFactors, (p : ℕ)) = S := by
    exact (Finset.prod_coe_sort S.primeFactors (fun p : ℕ => p)).trans
      (Nat.prod_primeFactors_of_squarefree hS)
  have hcop : Pairwise (fun p q : S.primeFactors => (p : ℕ).Coprime (q : ℕ)) := by
    intro p q hpq
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors p.2)
      (Nat.prime_of_mem_primeFactors q.2)).mpr (fun hp => hpq (Subtype.ext hp))
  exact (ZMod.ringEquivCongr hprod.symm).trans (ZMod.prodEquivPi (fun p : S.primeFactors => (p : ℕ)) hcop)

/-- Literal CRT cardinality of the special-linear group. -/
theorem squarefree_SL_two_card_prod {S : ℕ} (hS : Squarefree S) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) =
      ∏ p : S.primeFactors, Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod (p : ℕ))) := by
  rw [Nat.card_congr (specialLinearRingEquiv (n := Fin 2) (squarefreeZModPrimeEquiv hS))]
  rw [Nat.card_congr (specialLinearPiEquiv (n := Fin 2) (fun p : S.primeFactors => ZMod (p : ℕ)))]
  exact Nat.card_pi

/-- The exact real special-linear order formula in PD (det:SL-order). -/
theorem squarefree_SL_two_card_real {S : ℕ} (hS : Squarefree S) :
    (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ) =
      (S : ℝ) ^ 3 * ∏ p ∈ S.primeFactors, (1 - 1 / (p : ℝ) ^ 2) := by
  classical
  let _ (p : S.primeFactors) : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
  have hcard := congrArg (fun n : ℕ => (n : ℝ)) (squarefree_SL_two_card_prod hS)
  rw [Nat.cast_prod] at hcard
  rw [hcard]
  simp_rw [finite_field_card_SL_two_real, ZMod.card]
  rw [Finset.prod_mul_distrib, Finset.prod_pow]
  have hprod : (∏ p : S.primeFactors, (p : ℝ)) = (S : ℝ) := by
    calc
      (∏ p : S.primeFactors, (p : ℝ)) = ∏ p ∈ S.primeFactors, (p : ℝ) :=
        Finset.prod_coe_sort S.primeFactors (fun p : ℕ => (p : ℝ))
      _ = (S : ℝ) := by rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hS]
  rw [hprod]
  congr 1
  exact Finset.prod_coe_sort S.primeFactors (fun p : ℕ => (1 - 1 / (p : ℝ) ^ 2))

end ArtinMatthews
