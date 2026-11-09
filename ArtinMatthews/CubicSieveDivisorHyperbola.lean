module

public import Mathlib.Data.Nat.Sqrt
public import OAI.NumberTheory.PrimeGaps.VaughanIdentity


set_option backward.privateInPublic true
@[expose] public section

/-! The literal divisor hyperbola with both short arms and the square overlap. -/

noncomputable section
namespace ArtinMatthews

open Finset
open scoped BigOperators

private def cubicSieveFactorPairs (A B X : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 A ×ˢ Icc 1 B).filter (fun p => p.1 * p.2 ≤ X)

private theorem cubicSieveFactorPairs_sum (A B X : ℕ) (F : ℕ → ℝ) :
    (∑ p ∈ cubicSieveFactorPairs A B X, F (p.1 * p.2)) =
      ∑ a ∈ Icc 1 A, ∑ b ∈ Icc 1 (min B (X / a)), F (a * b) := by
  rw [cubicSieveFactorPairs, sum_filter, sum_product]
  apply sum_congr rfl
  intro a ha
  rw [← sum_filter]
  apply sum_congr _ (fun _ _ => rfl)
  ext b
  have hapos : 0 < a := (mem_Icc.mp ha).1
  simp only [mem_filter, mem_Icc, le_min_iff]
  rw [Nat.mul_comm a b, ← Nat.le_div_iff_mul_le hapos]
  tauto

private theorem cubicSieveFactorPairs_swap (A B X : ℕ) (F : ℕ → ℝ) :
    (∑ p ∈ cubicSieveFactorPairs A B X, F (p.1 * p.2)) =
      ∑ p ∈ cubicSieveFactorPairs B A X, F (p.1 * p.2) := by
  apply sum_equiv (Equiv.prodComm ℕ ℕ)
  · rintro ⟨a, b⟩
    simp only [cubicSieveFactorPairs, mem_filter, mem_product, Equiv.prodComm_apply,
      Prod.swap]
    rw [Nat.mul_comm b a]
    tauto
  · rintro ⟨a, b⟩ _
    exact congrArg F (Nat.mul_comm a b)

private theorem cubicSieveFactorPairs_short (X : ℕ) (F : ℕ → ℝ) :
    (∑ p ∈ cubicSieveFactorPairs X X X, F (p.1 * p.2)) =
      2 * (∑ a ∈ Icc 1 X.sqrt, ∑ b ∈ Icc 1 (X / a), F (a * b)) -
        ∑ a ∈ Icc 1 X.sqrt, ∑ b ∈ Icc 1 X.sqrt, F (a * b) := by
  let m := X.sqrt
  have hmX : m ≤ X := Nat.sqrt_le_self X
  have hUnion :
      cubicSieveFactorPairs m X X ∪ cubicSieveFactorPairs X m X =
        cubicSieveFactorPairs X X X := by
    ext ⟨a, b⟩
    simp only [cubicSieveFactorPairs, mem_union, mem_filter, mem_product, mem_Icc]
    constructor
    · rintro (⟨⟨ha, hb⟩, hab⟩ | ⟨⟨ha, hb⟩, hab⟩)
      · exact ⟨⟨⟨ha.1, ha.2.trans hmX⟩, hb⟩, hab⟩
      · exact ⟨⟨ha, ⟨hb.1, hb.2.trans hmX⟩⟩, hab⟩
    · rintro ⟨⟨ha, hb⟩, hab⟩
      have hsmall : a ≤ (a * b).sqrt ∨ b ≤ (a * b).sqrt :=
        Nat.le_sqrt_of_eq_mul rfl
      rcases hsmall with h | h
      · exact Or.inl ⟨⟨⟨ha.1, h.trans (Nat.sqrt_le_sqrt hab)⟩, hb⟩, hab⟩
      · exact Or.inr ⟨⟨ha, ⟨hb.1, h.trans (Nat.sqrt_le_sqrt hab)⟩⟩, hab⟩
  have hInter :
      cubicSieveFactorPairs m X X ∩ cubicSieveFactorPairs X m X =
        Icc 1 m ×ˢ Icc 1 m := by
    ext ⟨a, b⟩
    simp only [cubicSieveFactorPairs, mem_inter, mem_filter, mem_product, mem_Icc]
    constructor
    · rintro ⟨⟨⟨ha, _⟩, _⟩, ⟨⟨_, hb⟩, _⟩⟩
      exact ⟨ha, hb⟩
    · rintro ⟨ha, hb⟩
      have hab : a * b ≤ X := (Nat.mul_le_mul ha.2 hb.2).trans (Nat.sqrt_le X)
      exact ⟨⟨⟨ha, ⟨hb.1, hb.2.trans hmX⟩⟩, hab⟩,
        ⟨⟨⟨ha.1, ha.2.trans hmX⟩, hb⟩, hab⟩⟩
  have h := sum_union_inter (s₁ := cubicSieveFactorPairs m X X)
    (s₂ := cubicSieveFactorPairs X m X) (f := fun p => F (p.1 * p.2))
  rw [hUnion, hInter, ← cubicSieveFactorPairs_swap m X X F,
    cubicSieveFactorPairs_sum m X X F, sum_product] at h
  simp only [min_eq_right (Nat.div_le_self X _)] at h
  exact eq_sub_iff_add_eq.mpr (h.trans (by ring))

theorem cubicSieve_divisorCount_hyperbola (X : ℕ) (F : ℕ → ℝ) :
    (∑ n ∈ Icc 1 X, (n.divisors.card : ℝ) * F n) =
      2 * (∑ a ∈ Icc 1 X.sqrt, ∑ b ∈ Icc 1 (X / a), F (a * b)) -
        ∑ a ∈ Icc 1 X.sqrt, ∑ b ∈ Icc 1 X.sqrt, F (a * b) := by
  have hpairs := congrArg Complex.re (OAI.LargePrimeGaps.sum_divisorsAntidiagonal_hyperbola
    X (fun a b => (F (a * b) : ℂ)))
  simp only [← Complex.ofReal_sum, Complex.ofReal_re] at hpairs
  calc
    _ = ∑ n ∈ Icc 1 X, ∑ p ∈ n.divisorsAntidiagonal, F (p.1 * p.2) := by
      apply sum_congr rfl
      intro n _
      have hcard : n.divisorsAntidiagonal.card = n.divisors.card := by
        rw [← Nat.map_div_right_divisors, card_map]
      rw [← hcard, ← nsmul_eq_mul, ← sum_const]
      apply sum_congr rfl
      intro p hp
      rw [(Nat.mem_divisorsAntidiagonal.mp hp).1]
    _ = ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 (X / a), F (a * b) := hpairs
    _ = ∑ p ∈ cubicSieveFactorPairs X X X, F (p.1 * p.2) := by
      rw [cubicSieveFactorPairs_sum]
      simp only [min_eq_right (Nat.div_le_self X _)]
    _ = _ := cubicSieveFactorPairs_short X F

end ArtinMatthews
