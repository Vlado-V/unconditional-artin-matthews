module

public import ArtinMatthews.MarkedMemoryEndpointFamily


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine global decomposition of every normalized finite tableau into
its bare endpoint family, ordered birth enumerations and copied-slot
orders. The inverse constructs the original local data, preserving all
literal decorations and tests. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
  (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)

abbrev MarkedMemoryEndpointDecoratedIndex :=
  Σ e : MarkedMemoryEndpointFamily (A := A) (n := n) hZ s,
    MarkedMemoryEndpointBirthOrders e.1 × (Fin n → J → Equiv.Perm (Fin pads))

def markedMemoryEndpointDecorationsEquiv :
    MarkedMemoryNormalizedHistoryIndex (A := A) (n := n) hZ s ≃
      MarkedMemoryEndpointDecoratedIndex (A := A) (n := n) hZ s where
  toFun i := ⟨markedMemoryEndpointFamilyOfIndex hZ s hempty i,
    markedMemoryEndpointOriginalBirths hZ i.1.1.1,i.1.2⟩
  invFun e := markedMemoryEndpointFamilyIndex hZ s e.1 e.2.1 e.2.2
  left_inv i := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      exact markedMemoryEndpointOriginal_rebuild hZ i.1.1.1
        (fun j => markedMemoryFiniteTableau_initial_empty hZ s i.1.1.1 i.1.1.2 hempty j)
    · rfl
  right_inv e := by
    rcases e with ⟨⟨d,hd⟩,births,order⟩
    cases d
    rfl

include hempty in
/-- Exact global reindexing keeps an arbitrary complete-history
functional attached to its reconstructed decorated family. -/
theorem markedMemoryEndpointDecorations_sum {R : Type*} [AddCommMonoid R]
    (F : MarkedMemoryNormalizedHistoryIndex (A := A) (n := n) hZ s → R) :
    (∑ i : MarkedMemoryNormalizedHistoryIndex (A := A) (n := n) hZ s,F i) =
      ∑ e : MarkedMemoryEndpointFamily (A := A) (n := n) hZ s,
        ∑ births : MarkedMemoryEndpointBirthOrders e.1,
          ∑ order : Fin n → J → Equiv.Perm (Fin pads),
            F (markedMemoryEndpointFamilyIndex hZ s e births order) := by
  rw [← Equiv.sum_comp (markedMemoryEndpointDecorationsEquiv hZ s hempty).symm]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro e _
  exact Fintype.sum_prod_type _

theorem markedMemoryEndpointCopiedOrders_card :
    Fintype.card (Fin n → J → Equiv.Perm (Fin pads)) = (pads.factorial ^ Fintype.card J)^n := by
  simp only [Fintype.card_fun,Fintype.card_perm,Fintype.card_fin]

end
end ArtinMatthews
