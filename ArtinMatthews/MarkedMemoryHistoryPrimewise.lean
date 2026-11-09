module

public import ArtinMatthews.MarkedMemoryHistoryActiveCoherence
public import ArtinMatthews.MarkedMemoryTiltPrimewiseCRT


set_option backward.privateInPublic true
@[expose] public section

/-! Actual chronological vertices in the finite primewise expansion.
The active-line condition is derived from the original nonzero weight.
Empty active sets retain their singleton baseline and two-ended orphan
sum, and every inactive index keeps its original damping factor. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s)

def markedMemoryHistoryVertexPositions : Fin (n+1) → ℤ × ℤ :=
  fun v => (markedMemoryHistoryVertexState hZ history v).1.1

theorem markedMemoryHistoryVertexPrimitive :
    ∀ v, IsCoprime (markedMemoryHistoryVertexPositions hZ history v).1
      (markedMemoryHistoryVertexPositions hZ history v).2 :=
  fun v => hZ _ (markedMemoryHistoryVertexState hZ history v).1.2

def markedMemoryHistoryVertexSlots : Fin (n+1) → MarkedRawActive P (pads+1) :=
  fun v => (markedMemoryHistoryVertexState hZ history v).2.1

def markedMemoryHistoryPrimeVisits (p : Nat.Primes) : Finset (Fin (n+1)) :=
  markedMemoryActiveVisits (markedMemoryHistoryVertexSlots hZ history) p

def markedMemoryHistoryPrimeLines (p : Nat.Primes) : Fin (n+1) → MarkedRawPrimeLine p :=
  markedMemoryPositionLines p (markedMemoryHistoryVertexPositions hZ history)
    (markedMemoryHistoryVertexPrimitive hZ history)

def markedMemoryHistoryPrimeFactor (q : ℝ) (p : Nat.Primes) : ℝ :=
  markedMemoryProjectiveFactor p q (markedMemoryHistoryVertexPositions hZ history)
    (markedMemoryHistoryVertexPrimitive hZ history) (markedMemoryHistoryPrimeVisits hZ history p)

def markedMemoryHistoryPrimeActiveFactor (q : ℝ) (p : Nat.Primes)
    (hA : (markedMemoryHistoryPrimeVisits hZ history p).Nonempty) : ℝ :=
  (1 / ((p : ℝ)+1)) *
    (markedMemoryPrefixGhost (markedMemoryEta q n) (markedMemoryHistoryPrimeLines hZ history p)
        ((markedMemoryHistoryPrimeVisits hZ history p).min' hA) *
      markedMemoryInternalDamping (markedMemoryHistoryPrimeVisits hZ history p)
        (markedMemoryEta q n) (markedMemoryHistoryPrimeLines hZ history p)
        ((markedMemoryHistoryPrimeVisits hZ history p).min' hA)
        ((markedMemoryHistoryPrimeVisits hZ history p).max' hA) *
      markedMemorySuffixGhost (markedMemoryEta q n) (markedMemoryHistoryPrimeLines hZ history p)
        ((markedMemoryHistoryPrimeVisits hZ history p).min' hA)
        ((markedMemoryHistoryPrimeVisits hZ history p).max' hA))

def markedMemoryHistoryPrimeOrphanFactor (q : ℝ) (p : Nat.Primes) : ℝ :=
  markedMemoryBaseline q n p + (1 / ((p : ℝ)+1)) *
    markedMemoryOrphanGhostSum (markedMemoryEta q n) (markedMemoryHistoryPrimeLines hZ history p)

/-- This branch records actual nonempty visits, not an imposed interval.
The orphan branch retains the exact empty-active baseline. -/
def markedMemoryHistoryPrimeExpansion (q : ℝ) (p : Nat.Primes) : ℝ :=
  if hA : (markedMemoryHistoryPrimeVisits hZ history p).Nonempty then
    markedMemoryHistoryPrimeActiveFactor hZ history q p hA
  else markedMemoryHistoryPrimeOrphanFactor hZ history q p

theorem markedMemoryHistoryPrimeVisits_eq_identityVisits
    (hempty : ∀ band, (s.2.2.1.1 band : ℕ) = 0)
    (hd : MarkedMemoryHistoryBirthDistinct hZ history)
    (a : MarkedMemoryHistoryAddress hZ history) :
    markedMemoryHistoryPrimeVisits hZ history (markedMemoryHistoryAddressPrime hZ history a) =
      markedMemoryHistoryIdentityVisits hZ history hempty a :=
  (markedMemoryHistory_identity_visits_eq hZ history hempty hd a).symm

theorem markedMemoryHistoryPrimeFactor_empty (q : ℝ) (p : Nat.Primes)
    (hA : markedMemoryHistoryPrimeVisits hZ history p = ∅) :
    markedMemoryHistoryPrimeFactor hZ history q p =
      markedMemoryHistoryPrimeOrphanFactor hZ history q p := by
  unfold markedMemoryHistoryPrimeFactor
  rw [hA, markedMemoryProjectiveFactor_empty]
  rfl

variable [DecidableEq J]
  (ν : (band : J) → ↥(P band) → ℝ) (V : J → ℝ)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
  (qStage : ℕ → ℝ) (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (j : ℕ)

theorem markedMemoryHistoryPrimeLines_coherent
    (hw : markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j history ≠ 0)
    (hempty : ∀ band, (s.2.2.1.1 band : ℕ) = 0)
    (hd : MarkedMemoryHistoryBirthDistinct hZ history)
    (p : Nat.Primes) (a : Fin (n+1)) (ha : a ∈ markedMemoryHistoryPrimeVisits hZ history p) :
    MarkedMemoryActiveCoherent (markedMemoryHistoryPrimeVisits hZ history p)
      (markedMemoryHistoryPrimeLines hZ history p) a :=
  markedMemoryHistory_active_coherent_of_weight_ne_zero ν V hZ ψ η d₀ Y Q ρ qStage χ n j
    history hw hempty hd p a ha

theorem markedMemoryHistoryPrimeFactor_active
    (hw : markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j history ≠ 0)
    (hempty : ∀ band, (s.2.2.1.1 band : ℕ) = 0)
    (hd : MarkedMemoryHistoryBirthDistinct hZ history)
    (q : ℝ) (p : Nat.Primes) (hA : (markedMemoryHistoryPrimeVisits hZ history p).Nonempty) :
    markedMemoryHistoryPrimeFactor hZ history q p =
      markedMemoryHistoryPrimeActiveFactor hZ history q p hA := by
  have hc := markedMemoryHistoryPrimeLines_coherent hZ history ν V ψ η d₀ Y Q ρ qStage χ j
    hw hempty hd p _ ((markedMemoryHistoryPrimeVisits hZ history p).min'_mem hA)
  unfold markedMemoryHistoryPrimeLines at hc
  unfold markedMemoryHistoryPrimeFactor
  rw [markedMemoryProjectiveFactor_active p q _ _ _ hA, ite_eq_left hc]
  rfl

/-- No separate line-coherence premise remains in the actual history
application of the primewise expansion. -/
theorem markedMemoryHistoryPrimeFactor_expansion
    (hw : markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j history ≠ 0)
    (hempty : ∀ band, (s.2.2.1.1 band : ℕ) = 0)
    (hd : MarkedMemoryHistoryBirthDistinct hZ history) (q : ℝ) (p : Nat.Primes) :
    markedMemoryHistoryPrimeFactor hZ history q p =
      markedMemoryHistoryPrimeExpansion hZ history q p := by
  unfold markedMemoryHistoryPrimeExpansion
  split_ifs with hA
  · exact markedMemoryHistoryPrimeFactor_active hZ history ν V ψ η d₀ Y Q ρ qStage χ j
      hw hempty hd q p hA
  · exact markedMemoryHistoryPrimeFactor_empty hZ history q p
      (Finset.not_nonempty_iff_eq_empty.mp hA)

/-- The source's endpoint square-root schedule on natural ghost indices. -/
def markedMemoryHistoryVisitSchedule (q : ℝ) (N t : ℕ) : ℝ :=
  if t = 0 ∨ t = N then Real.sqrt q else q

theorem markedMemoryHistoryVisitSchedule_vertex (q : ℝ) (v : Fin (n+1)) :
    markedMemoryHistoryVisitSchedule q n v.val = markedMemoryVisitQ q n v := rfl

end
end ArtinMatthews
