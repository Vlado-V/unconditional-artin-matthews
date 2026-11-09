module

public import ArtinMatthews.MarkedMemoryHistoryLifespanScalarLines
public import ArtinMatthews.MarkedMemoryHistoryLifespanScalarEvents


set_option backward.privateInPublic true
@[expose] public section

/-! Exact source-schedule scalar factors, grouped by the actual indexed
lifespan. Birth and deletion factors are -eta times the literal line hit;
survival factors are 1-eta times that hit. These are the endpoint and
internal monomials used by the prefix/suffix/orphan expansions. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s)

def markedMemoryHistoryGhostSourceScalar (q : ℝ)
    (event : MarkedMemoryHistoryGhostScalarEvent hZ history) : ℝ :=
  let e := markedMemoryEta q n event.1
  let hit := markedMemoryHistoryAddressLineHit hZ history
    (markedMemoryHistoryGhostScalarOrigin hZ history event) event.1
  match event.2 with
  | Sum.inl old =>
      if old.2 ∈ (markedMemoryHistoryVertexGhost hZ history event.1).deletion old.1
      then -e*hit else 1-e*hit
  | Sum.inr _ => -e*hit

def markedMemoryHistoryLifespanSourceScalar (q : ℝ)
    (a : MarkedMemoryHistoryTraceAddress hZ history) : ℝ :=
  ∏ event : {event : MarkedMemoryHistoryGhostScalarEvent hZ history //
      markedMemoryHistoryGhostScalarOrigin hZ history event = a},
    markedMemoryHistoryGhostSourceScalar hZ history q event.1

omit [DecidableEq J] in
theorem markedMemoryHistoryGhostEventScalar_source
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history) (q : ℝ)
    (event : MarkedMemoryHistoryGhostScalarEvent hZ history) :
    markedMemoryHistoryGhostEventScalar hZ history (markedMemoryHistoryVisitSchedule q n) 0 event =
      markedMemoryHistoryGhostSourceScalar hZ history q event := by
  rw [markedMemoryHistoryGhostEventScalar_line hZ history ha]
  unfold markedMemoryHistoryGhostLineScalar markedMemoryHistoryGhostSourceScalar
  rw [Nat.zero_add, markedMemoryHistoryVisitSchedule_vertex]
  rfl

theorem markedMemoryHistoryLifespanScalar_source
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history) (q : ℝ)
    (a : MarkedMemoryHistoryTraceAddress hZ history) :
    markedMemoryHistoryLifespanScalar hZ history (markedMemoryHistoryVisitSchedule q n) 0 a =
      markedMemoryHistoryLifespanSourceScalar hZ history q a := by
  unfold markedMemoryHistoryLifespanScalar markedMemoryHistoryLifespanSourceScalar
  apply Finset.prod_congr rfl
  intro event _
  exact markedMemoryHistoryGhostEventScalar_source hZ history ha q event.1

def markedMemoryHistoryGhostPrimewiseScalar (q : ℝ) (p : Nat.Primes) (v₀ : Fin (n+1))
    (event : MarkedMemoryHistoryGhostScalarEvent hZ history) : ℝ :=
  let e := markedMemoryEta q n event.1
  let hit := markedLineHit (markedMemoryHistoryPrimeLines hZ history p) event.1
    (markedMemoryHistoryPrimeLines hZ history p v₀)
  match event.2 with
  | Sum.inl old =>
      if old.2 ∈ (markedMemoryHistoryVertexGhost hZ history event.1).deletion old.1
      then -e*hit else 1-e*hit
  | Sum.inr _ => -e*hit

omit [DecidableEq J] in
theorem markedMemoryHistoryGhostSourceScalar_primewise
    (a : MarkedMemoryHistoryTraceAddress hZ history) (p : Nat.Primes) (v₀ : Fin (n+1))
    (href : markedMemoryHistoryTraceAddressAnchor hZ history a =
      ⟨p, markedMemoryHistoryPrimeLines hZ history p v₀⟩)
    (q : ℝ) (event : MarkedMemoryHistoryGhostScalarEvent hZ history)
    (he : markedMemoryHistoryGhostScalarOrigin hZ history event = a) :
    markedMemoryHistoryGhostSourceScalar hZ history q event =
      markedMemoryHistoryGhostPrimewiseScalar hZ history q p v₀ event := by
  unfold markedMemoryHistoryGhostSourceScalar markedMemoryHistoryGhostPrimewiseScalar
  rw [he, markedMemoryHistoryAddressLineHit_eq_primewise hZ history a p v₀ href]

/-- An actual active visit fixes exactly the line used in the primewise
prefix, internal and suffix factors of this indexed lifespan. -/
theorem markedMemoryHistoryLifespanSourceScalar_active
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history)
    (a : MarkedMemoryHistoryTraceAddress hZ history) (v₀ : Fin (n+1)) (band : J) (k : Fin (pads+1))
    (hv : markedMemoryHistoryGhostSourceOrigin hZ history v₀ (Sum.inl ⟨band,k⟩) = a) (q : ℝ) :
    markedMemoryHistoryLifespanSourceScalar hZ history q a =
      ∏ event : {event : MarkedMemoryHistoryGhostScalarEvent hZ history //
          markedMemoryHistoryGhostScalarOrigin hZ history event = a},
        markedMemoryHistoryGhostPrimewiseScalar hZ history q
          ((markedMemoryHistoryVertexState hZ history v₀).2.1 band k).1 v₀ event.1 := by
  have href := markedMemoryHistoryGhostSourceOrigin_anchor hZ history ha v₀ (Sum.inl ⟨band,k⟩)
  rw [hv] at href
  unfold markedMemoryHistoryLifespanSourceScalar
  apply Finset.prod_congr rfl
  intro event _
  exact markedMemoryHistoryGhostSourceScalar_primewise hZ history a _ v₀ href q event.1 event.2

/-- A ghost-born identity uses its actual birth line as the reference,
including when it has no active visit (the orphan case). -/
theorem markedMemoryHistoryLifespanSourceScalar_ghost_birth
    (v₀ : Fin (n+1)) (birth : MarkedMemoryGhostBirthIndex (markedMemoryHistoryVertexGhost hZ history v₀))
    (q : ℝ) :
    let a := markedMemoryHistoryGhostScalarOrigin hZ history ⟨v₀, Sum.inr birth⟩
    markedMemoryHistoryLifespanSourceScalar hZ history q a =
      ∏ event : {event : MarkedMemoryHistoryGhostScalarEvent hZ history //
          markedMemoryHistoryGhostScalarOrigin hZ history event = a},
        markedMemoryHistoryGhostPrimewiseScalar hZ history q
          (markedMemoryGhostBirthPrime (markedMemoryHistoryVertexGhost hZ history v₀) birth) v₀ event.1 := by
  dsimp only
  have href : markedMemoryHistoryTraceAddressAnchor hZ history
      (markedMemoryHistoryGhostScalarOrigin hZ history ⟨v₀, Sum.inr birth⟩) =
      ⟨markedMemoryGhostBirthPrime (markedMemoryHistoryVertexGhost hZ history v₀) birth,
        markedMemoryHistoryPrimeLines hZ history
          (markedMemoryGhostBirthPrime (markedMemoryHistoryVertexGhost hZ history v₀) birth) v₀⟩ := by
    change markedMemoryHistoryTraceBirthAnchor hZ history _ _ = _
    rw [markedMemoryHistoryGhostTraceBirth_anchor]
    rfl
  unfold markedMemoryHistoryLifespanSourceScalar
  apply Finset.prod_congr rfl
  intro event _
  exact markedMemoryHistoryGhostSourceScalar_primewise hZ history _ _ v₀ href q event.1 event.2

theorem markedMemoryHistoryResidual_source_lifespanScalar
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (q : ℝ) :
    markedMemoryHistoryResidual hZ ψ η d₀ Y Q (markedMemoryHistoryVisitSchedule q n) χ n 0 history =
      (((∏ a : MarkedMemoryHistoryTraceAddress hZ history,
          markedMemoryHistoryLifespanSourceScalar hZ history q a) /
          markedMemoryHistoryBirthFactorials hZ history : ℝ) : ℂ) *
        markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n 0 history := by
  rw [markedMemoryHistoryResidual_lifespanScalar]
  simp_rw [markedMemoryHistoryLifespanScalar_source hZ history ha]

/-- The final scalar bridge requires the literal nonzero coefficient,
not a supplied line-coherence condition, and no numeric birth distinctness. -/
theorem markedMemoryHistoryResidual_source_lifespanScalar_of_weight_ne_zero
    (ν : (band : J) → ↥(P band) → ℝ) (V : J → ℝ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (q : ℝ)
    (hw : markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ
      (markedMemoryHistoryVisitSchedule q n) χ n 0 history ≠ 0) :
    markedMemoryHistoryResidual hZ ψ η d₀ Y Q (markedMemoryHistoryVisitSchedule q n) χ n 0 history =
      (((∏ a : MarkedMemoryHistoryTraceAddress hZ history,
          markedMemoryHistoryLifespanSourceScalar hZ history q a) /
          markedMemoryHistoryBirthFactorials hZ history : ℝ) : ℂ) *
        markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n 0 history :=
  markedMemoryHistoryResidual_source_lifespanScalar hZ history
    (markedMemoryHistoryAnchorAdmissible_of_weight_ne_zero ν V hZ ψ η d₀ Y Q ρ
      (markedMemoryHistoryVisitSchedule q n) χ n 0 history hw) ψ η d₀ Y Q χ q

end
end ArtinMatthews
