module

public import ArtinMatthews.MarkedMemoryHistoryRunWeight
public import ArtinMatthews.MarkedMemoryHistoryGroups


set_option backward.privateInPublic true
@[expose] public section

/-! An actual promotion preserves its band as well as its lifespan
identity. Thus the grouped retrieval mass is precisely one inverse V
factor for each actual promotion of that identity. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)

omit [DecidableEq J] in
theorem markedMemoryHistoryPromotionSource_group {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (r : MarkedMemoryHistoryPromotionIndex hZ history) :
    markedMemoryPopulationGroup (markedMemoryHistoryTraceState hZ history (markedMemoryHistoryPromotionTime hZ history r))
        (markedMemoryHistoryPromotionSource hZ history r) = markedMemoryHistoryPromotionGroup hZ history r := by
  induction n generalizing s with
  | zero => exact PEmpty.elim r
  | succ n ih =>
    cases r with
    | inl r => rfl
    | inr r => exact ih history.2.2 r

omit [DecidableEq J] in
theorem markedMemoryHistoryPromotionOrigin_group {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (r : MarkedMemoryHistoryPromotionIndex hZ history) :
    markedMemoryHistoryTraceAddressGroup hZ history (markedMemoryHistoryPromotionOrigin hZ history r) =
      markedMemoryHistoryPromotionGroup hZ history r := by
  exact (markedMemoryHistoryTraceOrigin_group hZ history _ _).trans
    (markedMemoryHistoryPromotionSource_group hZ history r)

/-- Exactly the number of actual old-memory retrievals of this computed
lifespan appears in its inverse-V exponent. -/
theorem markedMemoryHistoryRunMass_pow {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (a : MarkedMemoryHistoryTraceAddress hZ history) :
    markedMemoryHistoryRunMass V hZ history a =
      (V (markedMemoryHistoryTraceAddressGroup hZ history a))⁻¹ ^ markedMemoryHistoryRunCount hZ history a := by
  classical
  unfold markedMemoryHistoryRunMass
  calc
    _ = ∏ _r : {r : MarkedMemoryHistoryPromotionIndex hZ history //
          markedMemoryHistoryPromotionOrigin hZ history r = a},
        (V (markedMemoryHistoryTraceAddressGroup hZ history a))⁻¹ := by
      apply Finset.prod_congr rfl
      intro r _
      have hg := markedMemoryHistoryPromotionOrigin_group hZ history r.1
      rw [r.2] at hg
      exact congrArg (fun j => (V j)⁻¹) hg.symm
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, markedMemoryHistoryRunCount]

theorem markedMemoryChronologicalWeight_run_powers
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
    (qStage : ℕ → ℝ) (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (n j : ℕ) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q 1 qStage χ n j history =
      ((∏ a : MarkedMemoryHistoryTraceAddress hZ history,
        markedMemoryHistoryTraceBirthMass ν V hZ history a *
          (V (markedMemoryHistoryTraceAddressGroup hZ history a))⁻¹ ^
            markedMemoryHistoryRunCount hZ history a : ℝ) : ℂ) *
        markedMemoryHistoryResidual hZ ψ η d₀ Y Q qStage χ n j history := by
  rw [markedMemoryChronologicalWeight_lifespan_factor]
  simp_rw [markedMemoryHistoryRunMass_pow]

end
end ArtinMatthews
