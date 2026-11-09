module

public import ArtinMatthews.MarkedPrescribedPrimeTuple
public import Mathlib.Data.Fin.Tuple.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Strict earlier-coordinate prime values of a genuinely typed finite
prime tuple. Appending the last draw preserves all earlier prefixes. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

def markedPrimeTuplePrefix {n : ℕ} {P : Fin n → Finset Nat.Primes}
    (t : (i : Fin n) → ↥(P i)) (i : Fin n) : Fin i.val → Nat.Primes :=
  fun j => (t ⟨j.val,j.isLt.trans i.isLt⟩).1

theorem markedPrimeTuplePrefix_snoc_castSucc {n : ℕ}
    {P : Fin (n+1) → Finset Nat.Primes}
    (t : (i : Fin n) → ↥(P i.castSucc)) (p : P (Fin.last n)) (i : Fin n) :
    markedPrimeTuplePrefix (Fin.snoc t p) i.castSucc=markedPrimeTuplePrefix t i := by
  funext j
  change ((Fin.snoc (α := fun k => ↥(P k)) t p) (Fin.castSucc ⟨j.val,j.isLt.trans i.isLt⟩)).1=
    (t ⟨j.val,j.isLt.trans i.isLt⟩).1
  rw [Fin.snoc_castSucc]

theorem markedPrimeTuplePrefix_snoc_last {n : ℕ}
    {P : Fin (n+1) → Finset Nat.Primes}
    (t : (i : Fin n) → ↥(P i.castSucc)) (p : P (Fin.last n)) :
    markedPrimeTuplePrefix (Fin.snoc t p) (Fin.last n)=(fun i => (t i).1) := by
  funext i
  change ((Fin.snoc (α := fun k => ↥(P k)) t p) i.castSucc).1=(t i).1
  rw [Fin.snoc_castSucc]

end
end ArtinMatthews
