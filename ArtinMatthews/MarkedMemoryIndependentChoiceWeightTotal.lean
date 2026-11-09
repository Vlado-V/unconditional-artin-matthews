module

public import ArtinMatthews.MarkedMemoryIndependentTiltChoiceWeight
public import ArtinMatthews.MarkedMemoryResidualSupport


set_option backward.privateInPublic true
@[expose] public section

/-! Full elementwise signed coefficient preservation, including zero
geometric terms. Anchor support is discharged from the literal residual;
it is not a hypothesis in these original weight identities. -/
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
  (hn : MarkedMemoryBirthNormalized hZ d) (order : Fin n → J → Equiv.Perm (Fin pads))
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
  (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)

local notation "H" => markedMemoryIndependentHistory hZ d order
local notation "s" => markedMemoryIndependentState hZ d 0 (Nat.zero_le n)

include hinj hempty hterminal hn in
theorem markedMemoryIndependent_choice_source_weight_all (atom : (j : J) → ↥(P j) → ℝ) (q : ℝ) :
    (markedRawStateMass atom s:ℂ)*markedMemoryChronologicalWeight atom (fun _ => 1) hZ ψ η d₀ Y Q 1
      (markedMemoryHistoryVisitSchedule q n) χ n 0 H=
      ((markedMemoryIndependentPrimeChoiceProduct hZ d hinj q atom/
        markedMemoryIndependentBirthFactorials hZ d:ℝ):ℂ)*
          markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n 0 H := by
  by_cases ha : MarkedMemoryHistoryAnchorAdmissible hZ H
  · exact markedMemoryIndependent_choice_source_weight hZ d hinj hempty hterminal hn order ha atom q ψ η d₀ Y Q χ
  · have hw : markedMemoryChronologicalWeight atom (fun _ => 1) hZ ψ η d₀ Y Q 1
        (markedMemoryHistoryVisitSchedule q n) χ n 0 H=0 := by
      by_contra hw
      exact ha (markedMemoryHistoryAnchorAdmissible_of_weight_ne_zero atom (fun _ => 1) hZ ψ η d₀ Y Q 1
        (markedMemoryHistoryVisitSchedule q n) χ n 0 H hw)
    rw [hw,markedMemoryHistoryEdgeResidual_zero_of_not_anchor hZ ψ η d₀ Y Q χ n 0 H ha]
    simp only [mul_zero]

include hinj hempty hterminal hn in
theorem markedMemoryIndependent_tilt_choice_source_weight_all (V : J → ℝ) (hV : ∀ j,V j≠0) (q : ℝ) :
    (markedRawStateMass (markedMemoryTiltAtoms (P := P) V q n) s:ℂ)*
      markedMemoryChronologicalWeight (markedMemoryTiltAtoms (P := P) V q n) V hZ ψ η d₀ Y Q 1
        (markedMemoryHistoryVisitSchedule q n) χ n 0 H=
      (markedPhysicalMass V (pads+1):ℂ)*(((∏ j,(V j)⁻¹:ℝ):ℂ)^n)*
        ((markedMemoryIndependentPrimeChoiceProduct hZ d hinj q (markedMemoryLineAtoms (P := P) q n)/
          markedMemoryIndependentBirthFactorials hZ d:ℝ):ℂ)*
            markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n 0 H := by
  by_cases ha : MarkedMemoryHistoryAnchorAdmissible hZ H
  · exact markedMemoryIndependent_tilt_choice_source_weight hZ d hempty hinj hterminal hn order ha V hV q ψ η d₀ Y Q χ
  · have hw : markedMemoryChronologicalWeight (markedMemoryTiltAtoms (P := P) V q n) V hZ ψ η d₀ Y Q 1
        (markedMemoryHistoryVisitSchedule q n) χ n 0 H=0 := by
      by_contra hw
      exact ha (markedMemoryHistoryAnchorAdmissible_of_weight_ne_zero _ V hZ ψ η d₀ Y Q 1
        (markedMemoryHistoryVisitSchedule q n) χ n 0 H hw)
    rw [hw,markedMemoryHistoryEdgeResidual_zero_of_not_anchor hZ ψ η d₀ Y Q χ n 0 H ha]
    simp only [mul_zero]

end
end ArtinMatthews
