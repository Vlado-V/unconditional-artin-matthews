module

public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeChoices


set_option backward.privateInPublic true
@[expose] public section

/-! The actual integer fresh product is the cast of the literal natural
prime product; this keeps finite-product casts explicit in row identities. -/
noncomputable section
namespace ArtinMatthews

def markedDirtyRawFreshIntegerProduct {R : Type*} [Fintype R]
    {P : R → Finset Nat.Primes} (fresh : (r : R) → ↥(P r)) : ℤ :=
  ((∏ r, ((fresh r).1:ℕ) : ℕ):ℤ)

theorem markedDirtyRawFreshIntegerProduct_eq {R : Type*} [Fintype R]
    {P : R → Finset Nat.Primes} (fresh : (r : R) → ↥(P r)) :
    markedDirtyRawFreshIntegerProduct fresh=(markedRawLastProduct fresh:ℤ) := rfl

end ArtinMatthews
