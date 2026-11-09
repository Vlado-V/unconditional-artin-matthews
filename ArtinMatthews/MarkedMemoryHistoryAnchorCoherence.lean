module

public import ArtinMatthews.MarkedMemoryHistoryTraceAnchors


set_option backward.privateInPublic true
@[expose] public section

/-! A nonzero literal chronological weight forces genuine projective-line
coherence at every active visit of an indexed identity. No coherence,
anchor-consistency or abstract history correspondence is assumed. -/
namespace ArtinMatthews
noncomputable section

 theorem markedMemoryHistoryTraceOrigin_anchor_of_weight_ne_zero
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (n j : ℕ) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s)
    (hw : markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j history ≠ 0)
    (t : ℕ) (i : MarkedMemoryPopulationIndex (markedMemoryHistoryTraceState hZ history t)) :
    markedMemoryHistoryTraceAddressAnchor hZ history
      (markedMemoryLineageOrigin (T := MarkedMemoryHistoryTracePopulation hZ history)
        (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history) t i) =
      markedMemoryPopulationAnchor hZ (markedMemoryHistoryTraceState hZ history t) i :=
  markedMemoryHistoryTraceOrigin_anchor hZ history
    (markedMemoryHistoryAnchorAdmissible_of_weight_ne_zero ν V hZ ψ η d₀ Y Q ρ qStage χ n j history hw) t i

/-- The anchor is explicitly the real birth/initial anchor. Every indexed
active visit has that same anchor under the actual nonzero-weight condition. -/
 theorem markedMemoryHistory_active_anchor_coherence
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (n j : ℕ) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s)
    (hw : markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j history ≠ 0)
    (a : MarkedMemoryHistoryTraceAddress hZ history) (t : ℕ) (band : J) (k : Fin (pads+1))
    (hi : markedMemoryLineageOrigin (T := MarkedMemoryHistoryTracePopulation hZ history)
      (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history)
        t (Sum.inl ⟨band,k⟩) = a) :
    (⟨((markedMemoryHistoryTraceState hZ history t).2.1 band k).1,
      markedPrimePositionLine (((markedMemoryHistoryTraceState hZ history t).2.1 band k).1 : ℕ)
        (markedMemoryHistoryTraceState hZ history t).1.1
        (hZ _ (markedMemoryHistoryTraceState hZ history t).1.2)⟩ : MarkedMemoryAnchoredPrime) =
      markedMemoryHistoryTraceAddressAnchor hZ history a :=
  markedMemoryHistoryTrace_active_anchor hZ history
    (markedMemoryHistoryAnchorAdmissible_of_weight_ne_zero ν V hZ ψ η d₀ Y Q ρ qStage χ n j history hw)
    a t band k hi

/-- Under the separately stated actual distinct-birth hypothesis, repeated
numeric prime visits also carry the same actual projective line. -/
 theorem markedMemoryHistory_prime_anchor_coherence
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (n j : ℕ) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s)
    (hw : markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j history ≠ 0)
    (hempty : ∀ band, (s.2.2.1.1 band : ℕ) = 0)
    (hd : MarkedMemoryHistoryBirthDistinct hZ history) (r t : ℕ)
    (i : MarkedMemoryPopulationIndex (markedMemoryHistoryTraceState hZ history r))
    (k : MarkedMemoryPopulationIndex (markedMemoryHistoryTraceState hZ history t))
    (hp : markedMemoryPopulationPrime (markedMemoryHistoryTraceState hZ history r) i =
      markedMemoryPopulationPrime (markedMemoryHistoryTraceState hZ history t) k) :
    markedMemoryPopulationAnchor hZ (markedMemoryHistoryTraceState hZ history r) i =
      markedMemoryPopulationAnchor hZ (markedMemoryHistoryTraceState hZ history t) k :=
  markedMemoryHistoryTrace_anchors_eq_of_prime_eq hZ history
    (markedMemoryHistoryAnchorAdmissible_of_weight_ne_zero ν V hZ ψ η d₀ Y Q ρ qStage χ n j history hw)
    hempty hd r t i k hp

end
end ArtinMatthews
