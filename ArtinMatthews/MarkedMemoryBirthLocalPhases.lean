module

public import ArtinMatthews.MarkedBirthLocalPhases
public import ArtinMatthews.MarkedMemoryBirthDistinctWeighted


set_option backward.privateInPublic true
@[expose] public section

/-! The exact equality-event phases on the original chronological history.
Every phase is evaluated where its birth is performed. Later states need
not retain a pivot value. Only operations in the moved-address image can
receive a nontrivial multiplier. -/

noncomputable section
namespace ArtinMatthews
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def markedMemoryBirthLocalProduct
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    {s : MarkedRawState P (pads+1) B Z} (h : MarkedMemoryChronologicalHistory hZ n s)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B n))
    (θ : MarkedMemoryPotentialAddress J (pads+1) B n → AddCircle (1:ℝ)) : ℂ :=
  ∏ a, markedBirthLocalMultiplier σ θ a (markedMemoryPotentialAddressValue hZ h a)

theorem markedMemoryBirthLocalProduct_integral
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    {s : MarkedRawState P (pads+1) B Z} (h : MarkedMemoryChronologicalHistory hZ n s)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B n)) :
    (∫ θ, markedMemoryBirthLocalProduct hZ h σ θ
      ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) =
        if MarkedBirthPermutationEvent (markedMemoryPotentialAddressValue hZ h) σ then 1 else 0 := by
  unfold markedMemoryBirthLocalProduct
  simp_rw [← markedBirthPermutationPhase_local]
  exact markedBirthPermutationPhase_integral _ σ

theorem markedMemoryBirthLocalProduct_split
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    {s : MarkedRawState P (pads+1) B Z} (h : MarkedMemoryChronologicalHistory hZ n s)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B n))
    (θ : MarkedMemoryPotentialAddress J (pads+1) B n → AddCircle (1:ℝ)) :
    markedMemoryBirthLocalProduct hZ h σ θ =
      (∏ j, ∏ k : Fin (pads+1), markedBirthLocalMultiplier σ θ (Sum.inl (j,k))
        (some ((s.2.1 j k).1))) *
      (∏ t : Fin (n+1), ∏ j, ∏ k : Fin B,
        markedBirthLocalMultiplier σ θ (Sum.inr (Sum.inl (t,(j,k))))
          (markedMemoryPotentialGhostValue hZ h t j k)) *
      (∏ t : Fin n, ∏ j, markedBirthLocalMultiplier σ θ (Sum.inr (Sum.inr (t,j)))
        (markedMemoryPotentialEdgeValue hZ h t j)) := by
  simp only [markedMemoryBirthLocalProduct,MarkedMemoryPotentialAddress,MarkedMemoryPotentialBirth,
    Fintype.prod_sum_type,Fintype.prod_prod_type,markedMemoryPotentialAddressValue]
  ring

theorem markedMemoryBirthGhostPhase_unmodified
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    {M B n : ℕ} {Z : Finset (ℤ × ℤ)} {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B n))
    (θ : MarkedMemoryPotentialAddress J M B n → AddCircle (1:ℝ)) (t : Fin (n+1))
    (ht : some (2*t.1) ∉ σ.support.image markedMemoryPotentialOperation)
    {s : MarkedRawState P M B Z} (c : MarkedMemoryGhostChoice hZ s) :
    (∏ j, ∏ k : Fin B, markedBirthLocalMultiplier σ θ (Sum.inr (Sum.inl (t,(j,k))))
      (markedMemoryGhostPotentialValue c j k)) = 1 := by
  apply Finset.prod_eq_one
  intro j _
  apply Finset.prod_eq_one
  intro k _
  exact markedBirthLocalMultiplier_unmodified markedMemoryPotentialOperation σ θ _ ht _ rfl _

theorem markedMemoryBirthEdgePhase_unmodified
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B n))
    (θ : MarkedMemoryPotentialAddress J (pads+1) B n → AddCircle (1:ℝ)) (t : Fin n)
    (ht : some (2*t.1+1) ∉ σ.support.image markedMemoryPotentialOperation)
    {s : MarkedRawState P (pads+1) B Z} (c : MarkedMemoryEdgeChoice hZ s) :
    (∏ j, markedBirthLocalMultiplier σ θ (Sum.inr (Sum.inr (t,j)))
      (markedMemoryEdgePotentialValue c j)) = 1 := by
  apply Finset.prod_eq_one
  intro j _
  exact markedBirthLocalMultiplier_unmodified markedMemoryPotentialOperation σ θ _ ht _ rfl _

end ArtinMatthews
