module

public import ArtinMatthews.GiantSignedWordDomain
public import ArtinMatthews.GiantSignedStateGhostGroupLinear


set_option backward.privateInPublic true
@[expose] public section

/-! The countable visit is linear on its proved exponential domain. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {M : ℕ}

theorem giantSignedChronologicalVisit_add
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ) (q ρ : ℝ)
    {f g : GiantSignedState PS PB M → ℂ}
    (hf : GiantSignedWordExponential f) (hg : GiantSignedWordExponential g) :
    giantSignedChronologicalVisit ν V q ρ (fun s => f s + g s) =
      fun s => giantSignedChronologicalVisit ν V q ρ f s +
        giantSignedChronologicalVisit ν V q ρ g s := by
  obtain ⟨Cf, uf, hCf, huf, hf⟩ := hf
  obtain ⟨Cg, ug, hCg, hug, hg⟩ := hg
  exact giantSignedStateGhostGroup_add PS ν hν V q ρ f g Cf uf Cg ug
    hCf huf hCg hug (fun s a m => hf (s,a,m)) (fun s a m => hg (s,a,m))

theorem giantSignedChronologicalVisit_sub
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ) (q ρ : ℝ)
    {f g : GiantSignedState PS PB M → ℂ}
    (hf : GiantSignedWordExponential f) (hg : GiantSignedWordExponential g) :
    giantSignedChronologicalVisit ν V q ρ (fun s => f s - g s) =
      fun s => giantSignedChronologicalVisit ν V q ρ f s -
        giantSignedChronologicalVisit ν V q ρ g s := by
  obtain ⟨Cf, uf, hCf, huf, hf⟩ := hf
  obtain ⟨Cg, ug, hCg, hug, hg⟩ := hg
  exact giantSignedStateGhostGroup_sub PS ν hν V q ρ f g Cf uf Cg ug
    hCf huf hCg hug (fun s a m => hf (s,a,m)) (fun s a m => hg (s,a,m))

theorem giantSignedChronologicalVisit_zero
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ : ℝ) :
    giantSignedChronologicalVisit ν V q ρ (fun _ : GiantSignedState PS PB M => 0) =
      fun _ => 0 :=
  giantSignedStateGhostApply_zero PS ν _ _ _

theorem giantSignedChronologicalVisit_finset_sum {I : Type*}
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ) (q ρ : ℝ)
    (T : Finset I) (f : I → GiantSignedState PS PB M → ℂ)
    (hf : ∀ i ∈ T, GiantSignedWordExponential (f i)) :
    giantSignedChronologicalVisit ν V q ρ (fun s => ∑ i ∈ T, f i s) =
      fun s => ∑ i ∈ T, giantSignedChronologicalVisit ν V q ρ (f i) s := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using giantSignedChronologicalVisit_zero ν V q ρ
  | @insert i T hi ih =>
      have hfi := hf i (Finset.mem_insert_self _ _)
      have hT : ∀ j ∈ T, GiantSignedWordExponential (f j) :=
        fun j hj => hf j (Finset.mem_insert_of_mem hj)
      simp only [Finset.sum_insert hi]
      rw [giantSignedChronologicalVisit_add ν hν V q ρ hfi
        (giantSignedWordExponential_finset_sum T f hT), ih hT]

end
end ArtinMatthews
