module

public import ArtinMatthews.MarkedMemoryActualHistoryReconstruction
public import ArtinMatthews.MarkedMemoryFiniteHistoryIndex
public import ArtinMatthews.MarkedMemoryFiniteHistory


set_option backward.privateInPublic true
@[expose] public section

/-! A nonzero actual history lies in the image of a genuine finite
independent-tableau index. The finite data store no original history;
coverage follows from the proved finite roundtrip and literal recovery. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s)
  (ha : MarkedMemoryHistoryAnchorAdmissible hZ history)

local notation "tableau" => markedMemoryActualTableau hZ history ha
local notation "order" => markedMemoryActualOrder hZ history ha

def markedMemoryActualFiniteTableau :
    MarkedMemoryFiniteTableau (A := MarkedMemoryActualFiber hZ history)
      (P := P) (pads := pads) (B := B) hZ n :=
  markedMemoryIndependent_toFinite hZ tableau

theorem markedMemoryActualFinite_initial :
    markedMemoryIndependentState hZ
      (markedMemoryFiniteTableau_toIndependent hZ (markedMemoryActualFiniteTableau hZ history ha))
      0 (Nat.zero_le n) = s :=
  (markedMemoryFinite_restore_state hZ tableau 0 (Nat.zero_le n)).trans
    (markedMemoryActualTableau_initial hZ history ha)

def markedMemoryActualFiniteIndex :
    MarkedMemoryFiniteHistoryIndex (A := MarkedMemoryActualFiber hZ history) (n := n) hZ s :=
  (⟨markedMemoryActualFiniteTableau hZ history ha,markedMemoryActualFinite_initial hZ history ha⟩,order)

theorem markedMemoryActualFinite_reconstruction :
    markedMemoryFiniteHistoryAssembly hZ s (markedMemoryActualFiniteIndex hZ history ha) = history := by
  have hrestore := markedMemoryFinite_restore_history_heq hZ tableau order
  have hold : HEq (markedMemoryIndependentHistory hZ tableau order) history :=
    (markedMemoryHistoryTransport_heq hZ (markedMemoryActualTableau_initial hZ history ha)
      (markedMemoryIndependentHistory hZ tableau order)).symm.trans
        (heq_of_eq (markedMemoryActualHistory_reconstruction hZ history ha))
  exact eq_of_heq ((markedMemoryHistoryTransport_heq hZ (markedMemoryActualFinite_initial hZ history ha)
    (markedMemoryIndependentHistory hZ
      (markedMemoryFiniteTableau_toIndependent hZ (markedMemoryActualFiniteTableau hZ history ha)) order)).trans
      (hrestore.trans hold))

include ha in
theorem markedMemoryActualFinite_covered :
    history ∈ Set.range (markedMemoryFiniteHistoryAssembly (A := MarkedMemoryActualFiber hZ history) (n := n) hZ s) :=
  ⟨markedMemoryActualFiniteIndex hZ history ha,markedMemoryActualFinite_reconstruction hZ history ha⟩

theorem markedMemoryActualFinite_exists_of_weight_ne_zero
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (j : ℕ)
    (hw : markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j history ≠ 0) :
    ∃ index : MarkedMemoryFiniteHistoryIndex (A := MarkedMemoryActualFiber hZ history) (n := n) hZ s,
      markedMemoryFiniteHistoryAssembly hZ s index = history := by
  let hadm := markedMemoryHistoryAnchorAdmissible_of_weight_ne_zero ν V hZ ψ η d₀ Y Q ρ qStage χ n j history hw
  exact ⟨markedMemoryActualFiniteIndex hZ history hadm,markedMemoryActualFinite_reconstruction hZ history hadm⟩

end
end ArtinMatthews
