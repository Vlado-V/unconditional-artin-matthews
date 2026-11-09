module

public import ArtinMatthews.MarkedMemoryCanonicalFiber


set_option backward.privateInPublic true
@[expose] public section

/-! Exact normalized assembly-fiber multiplicity, derived from the
constructed canonical-extraction bijection. Only actual indexed
identities are counted; repeated numeric prime values are permitted. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
  (history : MarkedMemoryChronologicalHistory hZ n s)

theorem markedMemoryNormalizedFiber_unique_labeling
    (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history)
    (i : MarkedMemoryNormalizedHistoryIndex (A := A) (n := n) hZ s)
    (hi : markedMemoryNormalizedHistoryAssembly hZ s i=history) :
    ∃! e : (j : J) → MarkedMemoryActualFiber hZ history j ≃ A j,
      markedMemoryCanonicalLabelIndex hZ s history hempty ha e=i := by
  obtain ⟨e,he⟩ := markedMemoryCanonicalLabelFiber_surjective hZ s history hempty ha ⟨i,hi⟩
  have hval := congrArg Subtype.val he
  refine ⟨e,hval,?_⟩
  intro e' he'
  exact markedMemoryCanonicalLabelIndex_injective hZ s history hempty ha (he'.trans hval.symm)

theorem markedMemoryNormalizedFiber_card_of_equiv
    (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history)
    (e₀ : (j : J) → MarkedMemoryActualFiber hZ history j ≃ A j) :
    Fintype.card {i : MarkedMemoryNormalizedHistoryIndex (A := A) (n := n) hZ s //
      markedMemoryNormalizedHistoryAssembly hZ s i=history}=
        ∏ j,(Fintype.card (A j)).factorial := by
  calc
    _ = Fintype.card ((j : J) → MarkedMemoryActualFiber hZ history j ≃ A j) :=
      (Fintype.card_congr (markedMemoryCanonicalFiberEquiv hZ s history hempty ha)).symm
    _ = Fintype.card ((j : J) → Equiv.Perm (A j)) :=
      Fintype.card_congr (Equiv.piCongrRight fun j => Equiv.equivCongr (e₀ j) (Equiv.refl (A j)))
    _ = _ := by simp only [Fintype.card_pi,Fintype.card_perm]

theorem markedMemoryNormalizedFiber_card_of_card_eq
    (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history)
    (hcard : ∀ j,Fintype.card (MarkedMemoryActualFiber hZ history j)=Fintype.card (A j)) :
    Fintype.card {i : MarkedMemoryNormalizedHistoryIndex (A := A) (n := n) hZ s //
      markedMemoryNormalizedHistoryAssembly hZ s i=history}=
        ∏ j,(Fintype.card (A j)).factorial :=
  markedMemoryNormalizedFiber_card_of_equiv hZ s history hempty ha (fun j => Fintype.equivOfCardEq (hcard j))

theorem markedMemoryNormalizedFiber_card_zero_of_card_ne
    (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history)
    (j : J) (hne : Fintype.card (MarkedMemoryActualFiber hZ history j)≠Fintype.card (A j)) :
    Fintype.card {i : MarkedMemoryNormalizedHistoryIndex (A := A) (n := n) hZ s //
      markedMemoryNormalizedHistoryAssembly hZ s i=history}=0 := by
  let : IsEmpty {i : MarkedMemoryNormalizedHistoryIndex (A := A) (n := n) hZ s //
      markedMemoryNormalizedHistoryAssembly hZ s i=history} := ⟨by
    intro i
    obtain ⟨e,_,_⟩ := markedMemoryNormalizedFiber_extraction hZ s history hempty ha i.1 i.2
    exact hne (Fintype.card_congr (e j))⟩
  exact Fintype.card_eq_zero

theorem markedMemoryNormalizedFiber_card_eq_if
    (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history) :
    Fintype.card {i : MarkedMemoryNormalizedHistoryIndex (A := A) (n := n) hZ s //
      markedMemoryNormalizedHistoryAssembly hZ s i=history}=
        if ∀ j,Fintype.card (MarkedMemoryActualFiber hZ history j)=Fintype.card (A j)
        then ∏ j,(Fintype.card (A j)).factorial else 0 := by
  split_ifs with hc
  · exact markedMemoryNormalizedFiber_card_of_card_eq hZ s history hempty ha hc
  · obtain ⟨j,hj⟩ := not_forall.mp hc
    exact markedMemoryNormalizedFiber_card_zero_of_card_ne hZ s history hempty ha j hj

theorem markedMemoryActualNormalizedFiber_card
    (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history) :
    Fintype.card {i : MarkedMemoryNormalizedHistoryIndex
      (A := MarkedMemoryActualFiber hZ history) (n := n) hZ s //
        markedMemoryNormalizedHistoryAssembly hZ s i=history}=
          ∏ j,(Fintype.card (MarkedMemoryActualFiber hZ history j)).factorial :=
  markedMemoryNormalizedFiber_card_of_equiv hZ s history hempty ha (fun _ => Equiv.refl _)

theorem markedMemoryActualNormalizedFiber_card_fin
    (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history) :
    Fintype.card {i : MarkedMemoryNormalizedHistoryIndex
      (A := fun j => Fin (Fintype.card (MarkedMemoryActualFiber hZ history j))) (n := n) hZ s //
        markedMemoryNormalizedHistoryAssembly hZ s i=history}=
          ∏ j,(Fintype.card (MarkedMemoryActualFiber hZ history j)).factorial := by
  simpa only [Fintype.card_fin] using markedMemoryNormalizedFiber_card_of_equiv hZ s history hempty ha
    (fun j => Fintype.equivFin (MarkedMemoryActualFiber hZ history j))

theorem markedMemoryActualNormalizedFiber_card_of_weight_ne_zero
    (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (k : ℕ)
    (hw : markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n k history ≠ 0) :
    Fintype.card {i : MarkedMemoryNormalizedHistoryIndex
      (A := MarkedMemoryActualFiber hZ history) (n := n) hZ s //
        markedMemoryNormalizedHistoryAssembly hZ s i=history}=
          ∏ j,(Fintype.card (MarkedMemoryActualFiber hZ history j)).factorial :=
  markedMemoryActualNormalizedFiber_card hZ s history hempty
    (markedMemoryHistoryAnchorAdmissible_of_weight_ne_zero ν V hZ ψ η d₀ Y Q ρ qStage χ n k history hw)

theorem markedMemoryActualNormalizedFiber_card_fin_of_weight_ne_zero
    (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (k : ℕ)
    (hw : markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n k history ≠ 0) :
    Fintype.card {i : MarkedMemoryNormalizedHistoryIndex
      (A := fun j => Fin (Fintype.card (MarkedMemoryActualFiber hZ history j))) (n := n) hZ s //
        markedMemoryNormalizedHistoryAssembly hZ s i=history}=
          ∏ j,(Fintype.card (MarkedMemoryActualFiber hZ history j)).factorial :=
  markedMemoryActualNormalizedFiber_card_fin hZ s history hempty
    (markedMemoryHistoryAnchorAdmissible_of_weight_ne_zero ν V hZ ψ η d₀ Y Q ρ qStage χ n k history hw)

theorem markedMemoryNormalizedFiber_card_eq_if_of_weight_ne_zero
    (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (k : ℕ)
    (hw : markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n k history ≠ 0) :
    Fintype.card {i : MarkedMemoryNormalizedHistoryIndex (A := A) (n := n) hZ s //
      markedMemoryNormalizedHistoryAssembly hZ s i=history}=
        if ∀ j,Fintype.card (MarkedMemoryActualFiber hZ history j)=Fintype.card (A j)
        then ∏ j,(Fintype.card (A j)).factorial else 0 :=
  markedMemoryNormalizedFiber_card_eq_if hZ s history hempty
    (markedMemoryHistoryAnchorAdmissible_of_weight_ne_zero ν V hZ ψ η d₀ Y Q ρ qStage χ n k history hw)

end
end ArtinMatthews
