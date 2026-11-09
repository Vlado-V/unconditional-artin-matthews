module

public import ArtinMatthews.GiantSignedStateGhost


set_option backward.privateInPublic true
@[expose] public section

/-! One exponential degree bound is retained across every finite
small-state and active-label fiber of the actual ghost row. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

omit [DecidableEq S] in
theorem giantSignedStateGhostApply_exponential {M : ℕ}
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (A C D : B → ℂ)
    (w : GiantSignedState PS PB M → ℂ)
    (Cf u : ℝ) (hCf : 0 ≤ Cf) (hu : 0 < u)
    (hw : ∀ s a m, ‖w (s, a, m)‖ ≤ Cf * u ^ (∑ g, m.1 g)) :
    ∃ Cf' u' : ℝ, 0 ≤ Cf' ∧ 0 < u' ∧
      ∀ s a m, ‖giantSignedStateGhostApply PS ν A C D w (s, a, m)‖ ≤
        Cf' * u' ^ (∑ g, m.1 g) := by
  classical
  let X := GiantTwoSidedResidueState PS M × MarkedPhysicalMarking PB M
  let F (x : X) (m : GiantSignedMemory PB) :=
    giantSignedGhostSimultaneousApply ν A C D (fun m' => w (x.1, x.2, m')) m
  have hx (x : X) : ∃ Cx ux : ℝ, 0 ≤ Cx ∧ 0 < ux ∧
      ∀ m, ‖F x m‖ ≤ Cx * ux ^ (∑ g, m.1 g) :=
    giantSignedGhostSimultaneous_exponential ν hν A C D (fun m => w (x.1, x.2, m))
      Cf u hCf hu (hw x.1 x.2)
  have hset : ∀ t : Finset X, ∃ Ct ut : ℝ, 0 ≤ Ct ∧ 0 < ut ∧
      ∀ x ∈ t, ∀ m, ‖F x m‖ ≤ Ct * ut ^ (∑ g, m.1 g) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        refine ⟨0, 1, by norm_num, by norm_num, ?_⟩
        intro x hx
        simp at hx
    | @insert x t _hxt ih =>
        obtain ⟨Cx, ux, hCx, hux, hb⟩ := hx x
        obtain ⟨Ct, ut, hCt, hut, ht⟩ := ih
        refine ⟨Cx + Ct, ux + ut, add_nonneg hCx hCt, add_pos hux hut, ?_⟩
        intro y hy m
        rcases Finset.mem_insert.mp hy with rfl | hy
        · refine (hb m).trans ?_
          exact mul_le_mul (le_add_of_nonneg_right hCt)
            (pow_le_pow_left₀ hux.le (le_add_of_nonneg_right hut.le) _)
            (pow_nonneg hux.le _) (add_nonneg hCx hCt)
        · refine (ht y hy m).trans ?_
          exact mul_le_mul (le_add_of_nonneg_left hCx)
            (pow_le_pow_left₀ hut.le (le_add_of_nonneg_left hux.le) _)
            (pow_nonneg hut.le _) (add_nonneg hCx hCt)
  obtain ⟨Cf', u', hCf', hu', hbound⟩ := hset Finset.univ
  refine ⟨Cf', u', hCf', hu', ?_⟩
  intro s a m
  exact hbound (s, a) (Finset.mem_univ _) m

end
end ArtinMatthews
