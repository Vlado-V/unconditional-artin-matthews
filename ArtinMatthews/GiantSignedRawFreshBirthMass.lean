module

public import ArtinMatthews.GiantSignedRawFreshBirthGate


set_option backward.privateInPublic true
@[expose] public section

/-! The chronological atom estimate is summed on the literal grouped
fresh tuple appearing in the raw edge coefficient. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {B : Type*} [Fintype B] [DecidableEq B] {PB : B → Finset ℕ}
    {k ell n H : ℕ}

private theorem rawFreshBirthGate_sum_eq
    (hPB : ∀ g p, p ∈ PB g → p.Prime) (ν : ∀ g, PB g → ℝ)
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H))
    (i : Fin n) (C : B → Finset (Fin k)) (T : (g : B) → Finset (Fin (ell+(C g).card)))
    (old : GiantSignedUniformBirthAddress B (k+ell) n H → Option Nat.Primes) :
    let I := Σ g : B, Fin ((T g)ᶜ).card
    letI : DecidableEq I := Classical.decEq I
    let e : I ↪ GiantSignedUniformBirthAddress B (k+ell) n H :=
      giantSignedRawFreshBirthEmbedding i C T
    (∑ fresh : GiantSignedPrimeTuple PB (fun g => ((T g)ᶜ).card),
      if giantSignedRawFreshBirthGate hPB σ i C T old fresh then
        ∏ g, ∏ j, ν g (fresh g j) else 0) =
      ∑ t : (a : I) → PB (giantSignedUniformBirthGroup (e a)),
        if GiantSignedUniformBirthConditionalGate σ (.edge i)
          (giantSignedUniformBirthConditionalValues hPB e old t)
        then ∏ a, ν (giantSignedUniformBirthGroup (e a)) (t a) else 0 := by
  dsimp only
  let I := Σ g : B, Fin ((T g)ᶜ).card
  letI : DecidableEq I := Classical.decEq I
  let A := GiantSignedUniformBirthAddress B (k+ell) n H
  let e : I ↪ A := giantSignedRawFreshBirthEmbedding i C T
  let E : (∀ a : I, PB (giantSignedUniformBirthGroup (e a))) ≃
      GiantSignedPrimeTuple PB (fun g => ((T g)ᶜ).card) :=
    Equiv.piCurry (fun g (_ : Fin ((T g)ᶜ).card) => PB g)
  let F (f : GiantSignedPrimeTuple PB (fun g => ((T g)ᶜ).card)) : ℝ :=
    if giantSignedRawFreshBirthGate hPB σ i C T old f then
      ∏ g, ∏ j, ν g (f g j) else 0
  change (∑ f, F f) = _
  rw [← E.sum_comp F]
  apply Finset.sum_congr rfl
  intro t _
  have ht : (fun a : I => (E t) a.1 a.2) = t := by
    funext a
    rcases a with ⟨g,j⟩
    rfl
  have hp : (∏ g, ∏ j, ν g ((E t) g j)) =
      ∏ a : I, ν (giantSignedUniformBirthGroup (e a)) (t a) :=
    (Fintype.prod_sigma (fun a : I => ν (giantSignedUniformBirthGroup (e a)) (t a))).symm
  change (if GiantSignedUniformBirthConditionalGate σ (.edge i)
      (giantSignedUniformBirthConditionalValues hPB e old (fun a : I => (E t) a.1 a.2))
    then ∏ g, ∏ j, ν g ((E t) g j) else 0) = _
  rw [ht, hp]

theorem giantSignedRawFreshBirthGate_mass
    (hPB : ∀ g p, p ∈ PB g → p.Prime)
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    {Δ mass : ℝ} (hΔ : 0 ≤ Δ) (hMass1 : 1 ≤ mass)
    (hatom : ∀ g p, ν g p ≤ Δ) (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ mass)
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H))
    (i : Fin n) (C : B → Finset (Fin k)) (T : (g : B) → Finset (Fin (ell+(C g).card)))
    (old : GiantSignedUniformBirthAddress B (k+ell) n H → Option Nat.Primes)
    (hold : ∀ a, giantSignedUniformBirthOperation (k+ell) n H a = .edge i → old a = none) :
    (∑ fresh : GiantSignedPrimeTuple PB (fun g => ((T g)ᶜ).card),
      if giantSignedRawFreshBirthGate hPB σ i C T old fresh then
        ∏ g, ∏ j, ν g (fresh g j) else 0) ≤
      Δ^(giantSignedUniformBirthStageNonpivots σ (.edge i)).card *
        ∏ g, mass^((T g)ᶜ).card := by
  let I := Σ g : B, Fin ((T g)ᶜ).card
  let e : I ↪ GiantSignedUniformBirthAddress B (k+ell) n H :=
    giantSignedRawFreshBirthEmbedding i C T
  rw [rawFreshBirthGate_sum_eq hPB ν σ i C T old]
  have hp : mass^(Fintype.card I) = ∏ g, mass^((T g)ᶜ).card := by
    simp only [I, Fintype.card_sigma, Fintype.card_fin, Finset.prod_pow_eq_pow_sum]
  rw [← hp]
  exact giantSignedUniformBirthConditional_mass (I := I) hPB ν hν hΔ hMass1
    hatom hMass σ (.edge i) e old hold

end
end ArtinMatthews
