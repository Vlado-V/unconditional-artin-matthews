module

public import ArtinMatthews.MarkedMemoryStageBirthMass
public import ArtinMatthews.MarkedMinorArcRawEdgeConditionalActual


set_option backward.privateInPublic true
@[expose] public section

/-! The chronological pivot gate on literal edge fresh labels. Every
promotion remains an absent birth. The gate is constant on each actual
fixed-label target fibre, including all stores and indexed promotions. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedMemoryEdgePivotFreshGate
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes} {M B N : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) (t : Fin N)
    (old : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes)
    (I : Finset J) (fresh : (j : ↥(Finset.univ \ I)) → ↥(P j.1)) : Prop :=
  markedMemoryStageBirthGate σ (2*t.1+2) old (markedMemoryEdgeStageDraw t I)
    (markedMemoryEdgeStageDraw_injective t I) fresh

def markedMemoryEdgePivotGate
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes} {M B N pads : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) (t : Fin N)
    (old : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes)
    {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (s : MarkedRawState P (pads+1) B Z) (c : MarkedRawEdgeChoice hZ s) : Prop :=
  markedMemoryEdgePivotFreshGate σ t old (markedDirtyEdgePromotedGroups c.promotions)
    (markedDirtyFixedEdgeChoiceCode hZ s (markedDirtyEdgePromotedGroups c.promotions) ⟨c,rfl⟩).2.2.2

set_option backward.isDefEq.respectTransparency false in
theorem markedMemoryEdgePivotGate_fiber
    {J : Type*} [Fintype J] [decJ : DecidableEq J] {P : J → Finset Nat.Primes} {M B N pads : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) (t : Fin N)
    (old : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes)
    {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (s : MarkedRawState P (pads+1) B Z) (I : Finset J) (store : J → Bool)
    (indices : MarkedRawPromotionTuple s.2.2 I)
    (fresh : (j : ↥(Finset.univ \ I)) → ↥(P j.1))
    (c : MarkedDirtyFixedEdgeChoice hZ s I)
    (hc : c∈markedDirtyMajorChoiceFiber hZ s I store indices fresh) :
    markedMemoryEdgePivotGate σ t old hZ s c.1 ↔ markedMemoryEdgePivotFreshGate σ t old I fresh := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  rcases c with ⟨c,hI⟩
  subst I
  have hf := congrArg (fun code => code.2.2) (Finset.mem_filter.mp hc).2
  change (markedDirtyFixedEdgeChoiceCode hZ s (markedDirtyEdgePromotedGroups c.promotions) ⟨c,rfl⟩).2.2.2=fresh at hf
  change markedMemoryEdgePivotFreshGate σ t old (markedDirtyEdgePromotedGroups c.promotions)
    (markedDirtyFixedEdgeChoiceCode hZ s (markedDirtyEdgePromotedGroups c.promotions) ⟨c,rfl⟩).2.2.2 ↔ _
  rw [hf]

theorem markedMemoryEdgePivot_fresh_mass_le
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (hν : ∀ j p,0 ≤ ν j p)
    {Δ D : ℝ} (hΔ : 0 ≤ Δ) (hD : 1 ≤ D)
    (hatom : ∀ j p,ν j p ≤ Δ) (hmass : ∀ j,(∑ p : P j,ν j p) ≤ D)
    {M B N : ℕ} (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) (t : Fin N)
    (old : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes) (I : Finset J) :
    (∑ fresh : (j : ↥(Finset.univ \ I)) → ↥(P j.1),
      if markedMemoryEdgePivotFreshGate σ t old I fresh then
        finiteProductMass (fun j : ↥(Finset.univ \ I) => ν j.1) fresh else 0) ≤
      Δ^(markedMemoryStageNonpivots σ (2*t.1+2)).card*D^(Fintype.card J) := by
  have h := markedMemoryStageBirth_mass_le ν hν hΔ hD hatom hmass σ (2*t.1+2) old
    (markedMemoryEdgeStageDraw t I) (markedMemoryEdgeStageDraw_injective t I)
  have h' : (∑ fresh : (j : ↥(Finset.univ \ I)) → ↥(P j.1),
      if markedMemoryEdgePivotFreshGate σ t old I fresh then
        finiteProductMass (fun j : ↥(Finset.univ \ I) => ν j.1) fresh else 0) ≤
      Δ^(markedMemoryStageNonpivots σ (2*t.1+2)).card*D^(Fintype.card ↥(Finset.univ \ I)) := by
    refine le_trans (le_of_eq ?_) h
    apply Finset.sum_congr (congrArg
      (fun inst : Fintype ((j : ↥(Finset.univ \ I)) → ↥(P j.1)) =>
        @Finset.univ ((j : ↥(Finset.univ \ I)) → ↥(P j.1)) inst)
      (Subsingleton.elim _ _))
    intro fresh _
    rfl
  apply h'.trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hΔ _)
  apply pow_le_pow_right₀ hD
  simpa only [Fintype.card_coe,Finset.card_univ] using
    Finset.card_le_card (Finset.subset_univ (Finset.univ \ I))

end ArtinMatthews
