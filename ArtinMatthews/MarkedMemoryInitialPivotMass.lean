module

public import ArtinMatthews.MarkedMemoryStageBirthMass


set_option backward.privateInPublic true
@[expose] public section

/-! Initial active slots are genuine independent tilted-prime draws.
The initial portion of the chronological pivot event costs one atom for
each of its selected nonpivots, with every ordered slot retained. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedMemoryInitialPivotGate
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes} {M B N : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N))
    (old : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes)
    (active : MarkedRawActive P M) : Prop :=
  markedMemoryStageBirthGate σ 0 old markedMemoryInitialDraw markedMemoryInitialDraw_injective
    (fun a => active a.1 a.2)

set_option backward.isDefEq.respectTransparency false in
theorem markedMemoryInitialPivot_mass_le
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (hν : ∀ j p,0 ≤ ν j p)
    {Δ D : ℝ} (hΔ : 0 ≤ Δ) (hD : 1 ≤ D)
    (hatom : ∀ j p,ν j p ≤ Δ) (hmass : ∀ j,(∑ p : P j,ν j p) ≤ D)
    {M B N : ℕ} (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N))
    (old : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes) :
    (∑ active : MarkedRawActive P M,
      if markedMemoryInitialPivotGate σ old active then markedRawActiveMass ν active else 0) ≤
      Δ^(markedMemoryStageNonpivots σ 0).card*D^(Fintype.card J*M) := by
  have h := markedMemoryStageBirth_mass_le ν hν hΔ hD hatom hmass σ 0 old
    markedMemoryInitialDraw markedMemoryInitialDraw_injective
  let E := Equiv.piCurry (fun j (_k : Fin M) => ↥(P j))
  have heq := E.sum_comp (fun active =>
    if markedMemoryInitialPivotGate σ old active then markedRawActiveMass ν active else 0)
  have heq' : (∑ active : MarkedRawActive P M,
      if markedMemoryInitialPivotGate σ old active then markedRawActiveMass ν active else 0) =
      ∑ u : (a : Σ _j : J,Fin M) → ↥(P a.1),
        if markedMemoryStageBirthGate σ 0 old markedMemoryInitialDraw markedMemoryInitialDraw_injective u
        then ∏ a,ν a.1 (u a) else 0 := by
    simpa only [E,Equiv.piCurry_apply,Sigma.curry,Sigma.eta,markedMemoryInitialPivotGate,markedRawActiveMass,Fintype.prod_sigma] using heq.symm
  rw [heq']
  refine le_trans (le_of_eq ?_) (h.trans_eq ?_)
  · apply Finset.sum_congr (by ext; simp only [Finset.mem_univ])
    intro u _
    rfl
  · simp [Fintype.card_sigma]

end ArtinMatthews
