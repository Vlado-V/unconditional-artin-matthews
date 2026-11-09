module

public import ArtinMatthews.MarkedMajorArcHighRough
public import ArtinMatthews.MarkedMajorArcHighPrimeNormalized


set_option backward.privateInPublic true
@[expose] public section

/-! The literal modulated prime-minus-rough long coefficient from the
major-arc argument, with exact character and length normalization. -/
namespace ArtinMatthews
open Finset

noncomputable def markedMajorCenteredCoefficient (W v : ℝ) (n : ℕ) : ℂ := by
  classical
  exact (n:ℂ)^((v:ℂ)*Complex.I) *
    ((if n.Prime then (1:ℂ) else 0) -
      (markedSieveEulerProduct W:ℂ)⁻¹*((Real.log n)⁻¹:ℝ)*
        (if ∀ p ∈ Nat.primesLE ⌊W⌋₊, ¬p∣n then (1:ℂ) else 0))

noncomputable def markedMajorCenteredSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (W modulation t H u v : ℝ) : ℂ :=
  (H:ℂ)⁻¹ * ∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊,
    markedMajorCenteredCoefficient W modulation n *
      (χ (n:ZMod q)*(n:ℂ)^((t:ℂ)*Complex.I))

 theorem marked_centered_coefficient_phase {q : ℕ} (χ : DirichletCharacter ℂ q)
    (W modulation t : ℝ) {n : ℕ} (hn : 0 < n) :
    markedMajorCenteredCoefficient W modulation n *
        (χ (n:ZMod q)*(n:ℂ)^((t:ℂ)*Complex.I)) =
      (if n.Prime then χ (n:ZMod q)*(n:ℂ)^(((t+modulation:ℝ):ℂ)*Complex.I) else 0) -
      (markedSieveEulerProduct W:ℂ)⁻¹*
        ((if ∀ p ∈ Nat.primesLE ⌊W⌋₊, ¬p∣n then (1:ℂ) else 0)*
          (((Real.log n)⁻¹:ℝ)*(χ (n:ZMod q)*(n:ℂ)^(((t+modulation:ℝ):ℂ)*Complex.I)))) := by
  classical
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hp : (n:ℂ)^((modulation:ℂ)*Complex.I)*(n:ℂ)^((t:ℂ)*Complex.I) =
      (n:ℂ)^(((t+modulation:ℝ):ℂ)*Complex.I) := by
    rw [← Complex.cpow_add _ _ hnC]
    congr 1
    push_cast
    ring
  unfold markedMajorCenteredCoefficient
  calc
    _ = ((if n.Prime then (1:ℂ) else 0) -
          (markedSieveEulerProduct W:ℂ)⁻¹*((Real.log n)⁻¹:ℝ)*
            (if ∀ p ∈ Nat.primesLE ⌊W⌋₊, ¬p∣n then (1:ℂ) else 0))*χ (n:ZMod q)*
        ((n:ℂ)^((modulation:ℂ)*Complex.I)*(n:ℂ)^((t:ℂ)*Complex.I)) := by ring
    _ = _ := by rw [hp]; split_ifs <;> ring

 theorem marked_centered_sum_eq {q : ℕ} (χ : DirichletCharacter ℂ q)
    (W modulation t H u v : ℝ) (hu : 0 ≤ u) :
    markedMajorCenteredSum χ W modulation t H u v =
      markedMajorNormalizedPrimeSum χ (t+modulation) H u v -
        markedRoughCharacterSum χ W (t+modulation) H u v := by
  classical
  have hsum : (∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, markedMajorCenteredCoefficient W modulation n *
      (χ (n:ZMod q)*(n:ℂ)^((t:ℂ)*Complex.I))) =
      (∑ n ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime,
        χ (n:ZMod q)*(n:ℂ)^(((t+modulation:ℝ):ℂ)*Complex.I)) -
      (markedSieveEulerProduct W:ℂ)⁻¹*
        ∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊,
          (if ∀ p ∈ Nat.primesLE ⌊W⌋₊, ¬p∣n then (1:ℂ) else 0)*
            (((Real.log n)⁻¹:ℝ)*(χ (n:ZMod q)*(n:ℂ)^(((t+modulation:ℝ):ℂ)*Complex.I))) := by
    rw [sum_filter,mul_sum,← sum_sub_distrib]
    apply sum_congr rfl
    intro n hn
    apply marked_centered_coefficient_phase
    have hun : u < n := (Nat.floor_lt hu).1 (mem_Ioc.mp hn).1
    exact_mod_cast (lt_of_le_of_lt hu hun)
  rw [markedMajorCenteredSum,hsum,markedMajorNormalizedPrimeSum,markedRoughCharacterSum]
  simp only [one_div,Complex.ofReal_mul,mul_inv_rev]
  ring

end ArtinMatthews
