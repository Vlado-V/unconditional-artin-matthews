module

public import ArtinMatthews.FiniteFourier
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! Exact fourth moments from finite character orthogonality. The
composite-modulus Kloosterman argument uses both additive frequencies. -/

namespace ArtinMatthews

open scoped BigOperators

noncomputable section

variable {G α : Type*} [AddCommGroup G] [Fintype G]

def doubleCharacterSum (A : Finset α) (f g : α → G)
    (χ ψ : AddChar G ℂ) : ℂ := ∑ a ∈ A, χ (f a) * ψ (g a)

theorem doubleCharacterSum_norm_sq (A : Finset α) (f g : α → G)
    (χ ψ : AddChar G ℂ) :
    (‖doubleCharacterSum A f g χ ψ‖ ^ 2 : ℂ) =
      ∑ a ∈ A, ∑ b ∈ A, χ (f a - f b) * ψ (g a - g b) := by
  classical
  rw [← Complex.mul_conj']
  unfold doubleCharacterSum
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  simp only [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj, map_mul]
  ring

def doubleCoincidencePairs [DecidableEq α] [DecidableEq G]
    (A : Finset α) (f g : α → G) : Finset (α × α) :=
  (A ×ˢ A).filter (fun ab => f ab.1 = f ab.2 ∧ g ab.1 = g ab.2)

/-- Parseval with two independent frequencies counts exact coincidences
of both coordinates; no inequality or equidistribution is assumed. -/
theorem doubleCharacterSum_parseval [DecidableEq α] [DecidableEq G]
    (A : Finset α) (f g : α → G) :
    (∑ χ : AddChar G ℂ, ∑ ψ : AddChar G ℂ,
      (‖doubleCharacterSum A f g χ ψ‖ ^ 2 : ℂ)) =
        (Fintype.card G : ℂ) ^ 2 * (doubleCoincidencePairs A f g).card := by
  classical
  simp_rw [doubleCharacterSum_norm_sq]
  have hswap : (∑ χ : AddChar G ℂ, ∑ ψ : AddChar G ℂ,
      ∑ a ∈ A, ∑ b ∈ A, χ (f a - f b) * ψ (g a - g b)) =
      ∑ a ∈ A, ∑ b ∈ A, ∑ χ : AddChar G ℂ, ∑ ψ : AddChar G ℂ,
        χ (f a - f b) * ψ (g a - g b) := by
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (AddChar G ℂ))) (t := A)]
  rw [hswap]
  have horth (a b : α) :
      (∑ χ : AddChar G ℂ, ∑ ψ : AddChar G ℂ, χ (f a - f b) * ψ (g a - g b)) =
      if f a = f b ∧ g a = g b then (Fintype.card G : ℂ) ^ 2 else 0 := by
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul, AddChar.sum_apply_eq_ite, sub_eq_zero]
    by_cases hf : f a = f b <;> by_cases hg : g a = g b <;> simp [hf, hg, pow_two]
  simp_rw [horth]
  rw [← Finset.sum_product (f := fun ab : α × α =>
    if f ab.1 = f ab.2 ∧ g ab.1 = g ab.2 then (Fintype.card G : ℂ)^2 else 0)]
  rw [← Finset.sum_filter]
  simp only [doubleCoincidencePairs, Finset.sum_const, nsmul_eq_mul]
  ring


omit [Fintype G] in
theorem doubleCharacterSum_sq [DecidableEq α] (A : Finset α) (f g : α → G)
    (χ ψ : AddChar G ℂ) :
    doubleCharacterSum A f g χ ψ ^ 2 =
      doubleCharacterSum (A ×ˢ A) (fun ab => f ab.1 + f ab.2)
        (fun ab => g ab.1 + g ab.2) χ ψ := by
  classical
  simp only [doubleCharacterSum, pow_two, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_product, AddChar.map_add_eq_mul]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- The fourth moment counts pairs of pairs with equal two-coordinate sums. -/
theorem doubleCharacterSum_fourth_moment [DecidableEq α] [DecidableEq G]
    (A : Finset α) (f g : α → G) :
    (∑ χ : AddChar G ℂ, ∑ ψ : AddChar G ℂ,
      (‖doubleCharacterSum A f g χ ψ‖ ^ 4 : ℂ)) =
      (Fintype.card G : ℂ)^2 *
        (doubleCoincidencePairs (A ×ˢ A) (fun ab => f ab.1 + f ab.2)
          (fun ab => g ab.1 + g ab.2)).card := by
  have hnorm (χ ψ : AddChar G ℂ) :
      (‖doubleCharacterSum A f g χ ψ‖ ^ 4 : ℂ) =
      (‖doubleCharacterSum (A ×ˢ A) (fun ab => f ab.1 + f ab.2)
        (fun ab => g ab.1 + g ab.2) χ ψ‖ ^ 2 : ℂ) := by
    rw [← doubleCharacterSum_sq, norm_pow]
    push_cast
    ring
  simp_rw [hnorm]
  exact doubleCharacterSum_parseval _ _ _

/-- The actual unit Kloosterman sum, with both additive frequencies modulo `m`. -/
def unitKloostermanSum (m : ℕ) [NeZero m] (h k : ZMod m) : ℂ :=
  doubleCharacterSum Finset.univ (fun u : (ZMod m)ˣ => (u : ZMod m))
    (fun u => (↑(u⁻¹) : ZMod m)) (AddChar.zmodAddEquiv h) (AddChar.zmodAddEquiv k)

/-- Ordered unit quadruples with equal sum and equal inverse sum. -/
def unitKloostermanQuadruples (m : ℕ) [NeZero m] :
    Finset (((ZMod m)ˣ × (ZMod m)ˣ) × ((ZMod m)ˣ × (ZMod m)ˣ)) :=
  doubleCoincidencePairs (Finset.univ ×ˢ Finset.univ)
    (fun ab => (ab.1 : ZMod m) + ab.2)
    (fun ab => (↑(ab.1⁻¹) : ZMod m) + ↑(ab.2⁻¹))

/-- Exact composite-modulus Kloosterman fourth moment. This holds for every
positive modulus, including moduli which are not prime or squarefree. -/
theorem unitKloostermanSum_fourth_moment (m : ℕ) [NeZero m] :
    (∑ h : ZMod m, ∑ k : ZMod m, (‖unitKloostermanSum m h k‖ ^ 4 : ℂ)) =
      (m : ℂ)^2 * (unitKloostermanQuadruples m).card := by
  classical
  unfold unitKloostermanSum unitKloostermanQuadruples
  have hm := doubleCharacterSum_fourth_moment (G := ZMod m) Finset.univ
    (fun u : (ZMod m)ˣ => (u : ZMod m)) (fun u => (↑(u⁻¹) : ZMod m))
  simp only [ZMod.card] at hm
  rw [← hm]
  let e := (AddChar.zmodAddEquiv (n := m)).toEquiv
  let F (χ ψ : AddChar (ZMod m) ℂ) :=
    (‖doubleCharacterSum Finset.univ (fun u : (ZMod m)ˣ => (u : ZMod m))
      (fun u => (↑(u⁻¹) : ZMod m)) χ ψ‖ ^ 4 : ℂ)
  change (∑ h, ∑ k, F (e h) (e k)) = ∑ χ, ∑ ψ, F χ ψ
  simp only [Equiv.sum_comp]
  exact e.sum_comp (fun χ => ∑ ψ, F χ ψ)

end
end ArtinMatthews
