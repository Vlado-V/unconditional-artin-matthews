module

public import ArtinMatthews.MarkedMemoryIndependentChoiceProduct
public import ArtinMatthews.MarkedMemoryUnitSourceWeight


set_option backward.privateInPublic true
@[expose] public section

/-! Exact signed original-history coefficient in the primewise choice
coordinates, with the genuine source mass, individual birth factorials
and ordered raw-edge residual kept visible. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (hinj : Function.Injective (markedMemoryIndependentPrime hZ d))
  (hempty : ∀ j,(d.lifespan j).initial=[])
  (hterminal : ∀ j,markedMemoryIndependentQueue hZ d (2*n+1) j=[])
  (hn : MarkedMemoryBirthNormalized hZ d)
  (order : Fin n → J → Equiv.Perm (Fin pads))
  (ha : MarkedMemoryHistoryAnchorAdmissible hZ (markedMemoryIndependentHistory hZ d order))
  (atom : (j : J) → ↥(P j) → ℝ) (q : ℝ)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
  (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)

local notation "H" => markedMemoryIndependentHistory hZ d order

include hinj hempty hterminal hn ha in
theorem markedMemoryIndependent_choice_source_weight :
    (markedRawStateMass atom (markedMemoryIndependentState hZ d 0 (Nat.zero_le n)):ℂ)*
      markedMemoryChronologicalWeight atom (fun _ => 1) hZ ψ η d₀ Y Q 1
        (markedMemoryHistoryVisitSchedule q n) χ n 0 H=
      ((markedMemoryIndependentPrimeChoiceProduct hZ d hinj q atom/
        markedMemoryIndependentBirthFactorials hZ d:ℝ):ℂ)*
          markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n 0 H := by
  rw [markedMemoryIndependent_unit_source_weight hZ d hempty order atom q ψ η d₀ Y Q χ,
    markedMemoryIndependentPrimeChoiceProduct_eq hZ d hinj hempty hterminal hn order ha q atom]

end
end ArtinMatthews
