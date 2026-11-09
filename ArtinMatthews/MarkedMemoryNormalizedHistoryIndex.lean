module

public import ArtinMatthews.MarkedMemoryActualFiniteTableau
public import ArtinMatthews.MarkedMemoryFiniteAnchorNormalization


set_option backward.privateInPublic true
@[expose] public section

/-! The finite assembly restricted to canonical birth anchors. Actual
nonzero histories with empty initial pending memory have a constructed
preimage; no coverage or fiber-bijection premise is stored in the index. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq

variable {J : Type*} [Fintype J] [DecidableEq J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)

def MarkedMemoryNormalizedHistoryIndex :=
  {i : MarkedMemoryFiniteHistoryIndex (A := A) (n := n) hZ s //
    markedMemoryFiniteAnchorNormalize hZ i.1.1.1=i.1.1.1}

instance markedMemoryNormalizedHistoryIndex_fintype :
    Fintype (MarkedMemoryNormalizedHistoryIndex (A := A) (n := n) hZ s) := by
  classical
  unfold MarkedMemoryNormalizedHistoryIndex
  infer_instance

def markedMemoryNormalizedHistoryAssembly
    (i : MarkedMemoryNormalizedHistoryIndex (A := A) (n := n) hZ s) :
    MarkedMemoryChronologicalHistory hZ n s := markedMemoryFiniteHistoryAssembly hZ s i.1

variable {s} (history : MarkedMemoryChronologicalHistory hZ n s)

def markedMemoryActualNormalizedIndex
    (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history) :
    MarkedMemoryNormalizedHistoryIndex (A := MarkedMemoryActualFiber hZ history) (n := n) hZ s :=
  ⟨markedMemoryActualFiniteIndex hZ history ha,
    (markedMemoryFiniteAnchorNormalize_admissible_fixed_iff hZ _).mpr
      (markedMemoryBirthNormalized_restore hZ (markedMemoryActualTableau hZ history ha)
        (markedMemoryActualTableau_birthNormalized hZ history hempty ha))⟩

theorem markedMemoryActualNormalizedIndex_reconstruction
    (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history) :
    markedMemoryNormalizedHistoryAssembly hZ s (markedMemoryActualNormalizedIndex hZ history hempty ha)=history :=
  markedMemoryActualFinite_reconstruction hZ history ha

theorem markedMemoryActualNormalizedIndex_exists_of_weight_ne_zero
    (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (k : ℕ)
    (hw : markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n k history ≠ 0) :
    ∃ i : MarkedMemoryNormalizedHistoryIndex (A := MarkedMemoryActualFiber hZ history) (n := n) hZ s,
      markedMemoryNormalizedHistoryAssembly hZ s i=history := by
  let ha := markedMemoryHistoryAnchorAdmissible_of_weight_ne_zero ν V hZ ψ η d₀ Y Q ρ qStage χ n k history hw
  exact ⟨markedMemoryActualNormalizedIndex hZ history hempty ha,
    markedMemoryActualNormalizedIndex_reconstruction hZ history hempty ha⟩

end
end ArtinMatthews
