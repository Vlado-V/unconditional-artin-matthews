module

public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.GroupTheory.OrderOfElement


set_option backward.privateInPublic true
@[expose] public section

/-! A faithful complex character of a group of order two is its unique
nontrivial character. -/
namespace ArtinMatthews
open scoped Classical
noncomputable section

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem character_eq_one_or_of_card_two (hc : Nat.card G = 2)
    (χ : G →* ℂˣ) (hχ : Function.Injective χ) (φ : G →* ℂˣ) :
    φ = 1 ∨ φ = χ := by
  obtain ⟨σ, hσ, huniq⟩ := (Nat.card_eq_two_iff' (1 : G)).mp hc
  have hcases (g : G) : g = 1 ∨ g = σ := by
    by_cases hg : g = 1
    · exact Or.inl hg
    · exact Or.inr (huniq g hg)
  have hsq : σ ^ Nat.card G = 1 := pow_card_eq_one'
  have hs : σ ^ 2 = 1 := by simpa only [hc] using hsq
  have hvalue (θ : G →* ℂˣ) : (θ σ : ℂ) ^ 2 = 1 := by
    have h : θ σ ^ 2 = 1 := by rw [← map_pow, hs, map_one]
    exact congrArg Units.val h
  have hcne : (χ σ : ℂ) ≠ 1 := by
    intro h
    apply hσ
    apply hχ
    exact (Units.ext h).trans (map_one χ).symm
  have hcval : (χ σ : ℂ) = -1 := (sq_eq_one_iff.mp (hvalue χ)).resolve_left hcne
  rcases sq_eq_one_iff.mp (hvalue φ) with hp | hp
  · left
    apply MonoidHom.ext
    intro g
    rcases hcases g with rfl | rfl
    · exact map_one φ
    · exact Units.ext hp
  · right
    apply MonoidHom.ext
    intro g
    rcases hcases g with rfl | rfl
    · rw [map_one, map_one]
    · exact Units.ext (hp.trans hcval.symm)

omit [Finite G] in
theorem faithfulCharacter_ne_one_of_card_two (hc : Nat.card G = 2)
    (χ : G →* ℂˣ) (hχ : Function.Injective χ) : χ ≠ 1 := by
  obtain ⟨σ, hσ, _⟩ := (Nat.card_eq_two_iff' (1 : G)).mp hc
  intro h
  apply hσ
  apply hχ
  rw [h]
  rfl

end
end ArtinMatthews
