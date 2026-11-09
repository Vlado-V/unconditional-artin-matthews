module

public import ArtinMatthews.MarkedPrescribedPrimeLaw


set_option backward.privateInPublic true
@[expose] public section

/-! Prescribed coordinates in the actual finite product prime integral.
This applies equally to initial slots and to a fixed ghost birth batch. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def MarkedPrimeTuplePrescribed {I : Type*} {P : I → Finset Nat.Primes}
    (S : Finset I) (ξ : I → Nat.Primes) (t : (i : I) → ↥(P i)) : Prop :=
  ∀ i ∈ S, (t i).1 = ξ i

theorem markedPrescribedPrimeTuple_mass {I : Type*} [Fintype I] [DecidableEq I]
    {P : I → Finset Nat.Primes} (ν : (i : I) → ↥(P i) → ℝ)
    {Δ : ℝ} (hΔ : Δ ≠ 0) (S : Finset I) (ξ : I → Nat.Primes)
    (t : (i : I) → ↥(P i)) (ht : MarkedPrimeTuplePrescribed S ξ t) :
    (∏ i, ν i (t i)) = Δ^S.card * ∏ i, markedPrescribedPrimeLaw ν Δ S ξ i (t i) := by
  classical
  have hprod : (∏ i : I, if i ∈ S then Δ else 1) = Δ^S.card := by simp
  rw [← hprod,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S
  · simp only [hi,ite_true,markedPrescribedPrimeLaw,ht i hi]
    field_simp
  · simp only [hi,ite_false,markedPrescribedPrimeLaw,one_mul]

theorem markedPrescribedPrimeTuple_sum_le {I : Type*} [Fintype I] [DecidableEq I]
    {P : I → Finset Nat.Primes} (ν : (i : I) → ↥(P i) → ℝ)
    (hν : ∀ i p, 0 ≤ ν i p) {Δ N : ℝ} (hΔ : 0 < Δ) (hN : 1 ≤ N)
    (hatom : ∀ i p, ν i p ≤ Δ) (hmass : ∀ i, (∑ p, ν i p) ≤ N)
    (S : Finset I) (ξ : I → Nat.Primes) :
    (∑ t : (i : I) → ↥(P i), if MarkedPrimeTuplePrescribed S ξ t then ∏ i, ν i (t i) else 0) ≤
      Δ^S.card * N^(Fintype.card I) := by
  classical
  have hν' := markedPrescribedPrimeLaw_nonneg ν hν hΔ.le S ξ
  have hm' := markedPrescribedPrimeLaw_sum_le ν hΔ hN hatom hmass S ξ
  calc
    _ ≤ Δ^S.card * ∑ t : (i : I) → ↥(P i), ∏ i, markedPrescribedPrimeLaw ν Δ S ξ i (t i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro t _
      by_cases ht : MarkedPrimeTuplePrescribed S ξ t
      · rw [ite_eq_left ht,markedPrescribedPrimeTuple_mass ν hΔ.ne' S ξ t ht]
      · rw [ite_eq_right ht]
        exact mul_nonneg (pow_nonneg hΔ.le _) (Finset.prod_nonneg (fun i _ => hν' i _))
    _ = Δ^S.card * ∏ i, ∑ p, markedPrescribedPrimeLaw ν Δ S ξ i p := by
      rw [Fintype.prod_sum]
    _ ≤ Δ^S.card * ∏ _i : I, N := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hΔ.le _)
      exact Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg (fun p _ => hν' i p)) (fun i _ => hm' i)
    _ = _ := by simp only [Finset.prod_const,Finset.card_univ]

end ArtinMatthews
