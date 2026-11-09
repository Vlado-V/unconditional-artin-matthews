module

public import ArtinMatthews.MarkedMemoryNormalizedHistoryIndex
public import ArtinMatthews.MarkedMemoryNormalizedLabelOrbit


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine factorial family inside each normalized assembly fiber.
The family is constructed by free relabeling. The resulting lower
bound does not replace the separate transitivity/upper-bound problem. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq

variable {J : Type*} [Fintype J] [DecidableEq J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)} {n : ℕ}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

omit [DecidableEq J] in
theorem markedMemoryFiniteRelabel_initial (e : (j : J) → Equiv.Perm (A j)) :
    markedMemoryIndependentState hZ
        (markedMemoryFiniteTableau_toIndependent hZ (markedMemoryFiniteRelabel hZ d e)) 0 (Nat.zero_le n)=
      markedMemoryIndependentState hZ d 0 (Nat.zero_le n) :=
  (markedMemoryFinite_restore_state hZ (markedMemoryIndependentRelabel hZ e d) 0 (Nat.zero_le n)).trans
    (markedMemoryIndependentRelabel_state hZ e d 0 (Nat.zero_le n))

variable (hn : MarkedMemoryBirthNormalized hZ d)
  (s : MarkedRawState P (pads+1) B Z)
  (hs : markedMemoryIndependentState hZ d 0 (Nat.zero_le n)=s)
  (order : Fin n → J → Equiv.Perm (Fin pads))

def markedMemoryNormalizedRelabelIndex (e : (j : J) → Equiv.Perm (A j)) :
    MarkedMemoryNormalizedHistoryIndex (A := A) (n := n) hZ s :=
  ⟨(⟨markedMemoryFiniteRelabel hZ d e,(markedMemoryFiniteRelabel_initial hZ d e).trans hs⟩,order),
    (markedMemoryNormalizedFiniteRelabel hZ d hn e).2⟩

omit [DecidableEq J] in
theorem markedMemoryNormalizedRelabelIndex_injective :
    Function.Injective (markedMemoryNormalizedRelabelIndex hZ d hn s hs order) := by
  intro e f h
  apply markedMemoryFiniteRelabel_injective hZ d
  exact congrArg (fun i : MarkedMemoryNormalizedHistoryIndex (A := A) (n := n) hZ s => i.1.1.1) h

omit [DecidableEq J] in
theorem markedMemoryNormalizedRelabelIndex_assembly (e : (j : J) → Equiv.Perm (A j)) :
    markedMemoryNormalizedHistoryAssembly hZ s (markedMemoryNormalizedRelabelIndex hZ d hn s hs order e)=
      markedMemoryHistoryTransport hZ hs (markedMemoryIndependentHistory hZ d order) := by
  apply eq_of_heq
  exact (markedMemoryHistoryTransport_heq hZ ((markedMemoryFiniteRelabel_initial hZ d e).trans hs) _).trans
    ((markedMemoryFiniteRelabel_history_heq hZ d e order).trans
      (markedMemoryHistoryTransport_heq hZ hs (markedMemoryIndependentHistory hZ d order)).symm)

theorem markedMemoryNormalizedRelabelIndex_functional_sum {R : Type*} [AddCommMonoid R]
    (F : MarkedMemoryChronologicalHistory hZ n s → R) :
    (∑ e : (j : J) → Equiv.Perm (A j),
      F (markedMemoryNormalizedHistoryAssembly hZ s (markedMemoryNormalizedRelabelIndex hZ d hn s hs order e))) =
        (∏ j,(Fintype.card (A j)).factorial) •
          F (markedMemoryHistoryTransport hZ hs (markedMemoryIndependentHistory hZ d order)) := by
  simp only [markedMemoryNormalizedRelabelIndex_assembly,Finset.sum_const,Finset.card_univ,
    Fintype.card_pi,Fintype.card_perm]

def markedMemoryNormalizedFiberEmbedding :
    ((j : J) → Equiv.Perm (A j)) ↪
      {i : MarkedMemoryNormalizedHistoryIndex (A := A) (n := n) hZ s //
        markedMemoryNormalizedHistoryAssembly hZ s i=
          markedMemoryHistoryTransport hZ hs (markedMemoryIndependentHistory hZ d order)} where
  toFun e := ⟨markedMemoryNormalizedRelabelIndex hZ d hn s hs order e,
    markedMemoryNormalizedRelabelIndex_assembly hZ d hn s hs order e⟩
  inj' := fun _ _ h => markedMemoryNormalizedRelabelIndex_injective hZ d hn s hs order
    (congrArg Subtype.val h)

include hn in
theorem markedMemoryNormalizedFiber_card_lower :
    (∏ j,(Fintype.card (A j)).factorial) ≤
      Fintype.card {i : MarkedMemoryNormalizedHistoryIndex (A := A) (n := n) hZ s //
        markedMemoryNormalizedHistoryAssembly hZ s i=
          markedMemoryHistoryTransport hZ hs (markedMemoryIndependentHistory hZ d order)} := by
  have h := Fintype.card_le_of_injective _ (markedMemoryNormalizedFiberEmbedding hZ d hn s hs order).injective
  simpa only [Fintype.card_pi,Fintype.card_perm] using h

theorem markedMemoryActualNormalizedFiber_card_lower
    (history : MarkedMemoryChronologicalHistory hZ n s)
    (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history) :
    (∏ j,(Fintype.card (MarkedMemoryActualFiber hZ history j)).factorial) ≤
      Fintype.card {i : MarkedMemoryNormalizedHistoryIndex
        (A := MarkedMemoryActualFiber hZ history) (n := n) hZ s //
          markedMemoryNormalizedHistoryAssembly hZ s i=history} := by
  have h := markedMemoryNormalizedFiber_card_lower hZ (markedMemoryActualTableau hZ history ha)
    (markedMemoryActualTableau_birthNormalized hZ history hempty ha) s
    (markedMemoryActualTableau_initial hZ history ha) (markedMemoryActualOrder hZ history ha)
  simpa only [markedMemoryActualHistory_reconstruction] using h

theorem markedMemoryActualNormalizedFiber_card_lower_of_weight_ne_zero
    (history : MarkedMemoryChronologicalHistory hZ n s)
    (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (k : ℕ)
    (hw : markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n k history ≠ 0) :
    (∏ j,(Fintype.card (MarkedMemoryActualFiber hZ history j)).factorial) ≤
      Fintype.card {i : MarkedMemoryNormalizedHistoryIndex
        (A := MarkedMemoryActualFiber hZ history) (n := n) hZ s //
          markedMemoryNormalizedHistoryAssembly hZ s i=history} :=
  markedMemoryActualNormalizedFiber_card_lower hZ s history hempty
    (markedMemoryHistoryAnchorAdmissible_of_weight_ne_zero ν V hZ ψ η d₀ Y Q ρ qStage χ n k history hw)

end
end ArtinMatthews
