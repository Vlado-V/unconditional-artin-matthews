module

public import ArtinMatthews.MarkedMemoryStageBirthMass
public import ArtinMatthews.MarkedMinorArcRawGhostConditionalActual


set_option backward.privateInPublic true
@[expose] public section

/-! Actual ghost batches pay one atom for each chronological nonpivot,
even when its earlier equal-value parent was drawn in this same batch.
The literal ordered-birth factorials are retained. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedMemoryGhostPivotGate
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes} {M B N : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) (t : Fin (N+1))
    (old : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes)
    (l : J → Fin (B+1)) (births : (j : J) → Fin (l j:ℕ) → ↥(P j)) : Prop :=
  markedMemoryStageBirthGate σ (2*t.1+1) old (markedMemoryGhostStageDraw t l)
    (markedMemoryGhostStageDraw_injective t l) (fun a => births a.1 a.2)

set_option backward.isDefEq.respectTransparency false in
theorem markedMemoryGhostPivot_tuple_mass_le
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (hν : ∀ j p,0 ≤ ν j p)
    {Δ D : ℝ} (hΔ : 0 ≤ Δ) (hD : 1 ≤ D)
    (hatom : ∀ j p,ν j p ≤ Δ) (hmass : ∀ j,(∑ p : P j,ν j p) ≤ D)
    {M B N : ℕ} (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) (t : Fin (N+1))
    (old : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes) (l : J → Fin (B+1)) :
    (∑ births : (j : J) → Fin (l j:ℕ) → ↥(P j),
      if markedMemoryGhostPivotGate σ t old l births then ∏ j,∏ k,ν j (births j k) else 0) ≤
      Δ^(markedMemoryStageNonpivots σ (2*t.1+1)).card*D^(∑ j,(l j:ℕ)) := by
  have h := markedMemoryStageBirth_mass_le ν hν hΔ hD hatom hmass σ (2*t.1+1) old
    (markedMemoryGhostStageDraw t l) (markedMemoryGhostStageDraw_injective t l)
  let E := Equiv.piCurry (fun j (_k : Fin (l j:ℕ)) => ↥(P j))
  have heq := E.sum_comp (fun births =>
    if markedMemoryGhostPivotGate σ t old l births then ∏ j,∏ k,ν j (births j k) else 0)
  have heq' : (∑ births : (j : J) → Fin (l j:ℕ) → ↥(P j),
      if markedMemoryGhostPivotGate σ t old l births then ∏ j,∏ k,ν j (births j k) else 0) =
      ∑ u : (a : Σ j,Fin (l j:ℕ)) → ↥(P a.1),
        if markedMemoryStageBirthGate σ (2*t.1+1) old (markedMemoryGhostStageDraw t l)
          (markedMemoryGhostStageDraw_injective t l) u then ∏ a,ν a.1 (u a) else 0 := by
    simpa only [E,Equiv.piCurry_apply,Sigma.curry,Sigma.eta,markedMemoryGhostPivotGate,Fintype.prod_sigma] using heq.symm
  rw [heq']
  refine le_trans (le_of_eq ?_) (h.trans_eq ?_)
  · apply Finset.sum_congr (by ext; simp only [Finset.mem_univ])
    intro u _
    rfl
  · simp only [Fintype.card_sigma,Fintype.card_fin]

theorem markedMemoryGhostPivot_factorial_mass_le
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (hν : ∀ j p,0 ≤ ν j p)
    {Δ D : ℝ} (hΔ : 0 ≤ Δ) (hD : 1 ≤ D)
    (hatom : ∀ j p,ν j p ≤ Δ) (hmass : ∀ j,(∑ p : P j,ν j p) ≤ D)
    {M B N : ℕ} (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) (t : Fin (N+1))
    (old : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes)
    (m : MarkedRawMemory P B) (del : MarkedRawGhostDeletion m) (l : MarkedRawGhostBirthSizes m del) :
    (∑ births : MarkedRawGhostBirthLabels l,
      if markedMemoryGhostPivotGate σ t old l.1 births then markedRawGhostBirthMass ν l births else 0) ≤
      Δ^(markedMemoryStageNonpivots σ (2*t.1+1)).card*
        ∏ j,D^(l.1 j:ℕ)/(Nat.factorial (l.1 j:ℕ):ℝ) := by
  have heq : (∑ births : MarkedRawGhostBirthLabels l,
      if markedMemoryGhostPivotGate σ t old l.1 births then markedRawGhostBirthMass ν l births else 0) =
      (∑ births : MarkedRawGhostBirthLabels l,
        if markedMemoryGhostPivotGate σ t old l.1 births then ∏ j,∏ k,ν j (births j k) else 0)/
          (∏ j,(Nat.factorial (l.1 j:ℕ):ℝ)) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro births _
    split_ifs
    · simp only [markedRawGhostBirthMass,Finset.prod_div_distrib]
    · exact (zero_div _).symm
  rw [heq]
  have hden : 0 ≤ (∏ j : J,(Nat.factorial (l.1 j:ℕ):ℝ)) :=
    Finset.prod_nonneg (fun j _ => Nat.cast_nonneg (Nat.factorial (l.1 j:ℕ)))
  have h := div_le_div_of_nonneg_right
    (markedMemoryGhostPivot_tuple_mass_le ν hν hΔ hD hatom hmass σ t old l.1)
    hden
  apply h.trans_eq
  rw [Finset.prod_div_distrib,Finset.prod_pow_eq_pow_sum]
  ring

end ArtinMatthews
