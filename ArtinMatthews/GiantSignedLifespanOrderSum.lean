module

public import ArtinMatthews.GiantSignedSelectedLifespanEquiv


set_option backward.privateInPublic true
@[expose] public section

/-! Removing the ordered ghost schedules cancels exactly the actual
birth factorials, on each fixed path and supported prime assignment. -/

namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

universe u

variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ)

local notation "Path" p => GiantSignedLifespanOriginalPath PS PB (ell := ell) (fun i => C i (Subtype.val (p i))) κ
local notation "Orders" => GiantSignedSelectedOrderedLifespan PS PB ell patterns C κ visitQ

theorem giantSignedSelectedOrderedLifespan_sum_birth_factor
    [∀ p : ((i : Fin n) → patterns i), Fintype (Path p)]
    (F : (p : ((i : Fin n) → patterns i)) → (path : Path p) → GiantSignedFixedLifespanChoices path visitQ → ℂ) :
    (∑ x : Orders,
      giantSignedChronologicalBirthFactor (fun i g => (giantSignedGhostVisitBorn (x.2.2.1.val g) i).card) *
        F x.1 x.2.1 x.2.2.1) =
      ∑ p : ((i : Fin n) → patterns i), ∑ path : Path p, ∑ c : GiantSignedFixedLifespanChoices path visitQ, F p path c := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro p _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro path _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c _
  exact giantSignedLifespanBirthOrderSchedule_sum_factor c.val (F p path c)

end
end ArtinMatthews
