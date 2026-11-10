module

public import ArtinMatthews.MarkedMemoryHistoryAnchors
public import ArtinMatthews.MarkedMemoryHistoryVisits
public import ArtinMatthews.MarkedMemoryHistoryAnchorCoherence
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual vertex visits satisfy the exact projective-line coherence
predicate used by the primewise memory factor. Its proof comes from the
literal nonzero chronological weight, with numeric identity identification
using only the separately stated initial boundary and birth distinctness. -/
namespace ArtinMatthews
noncomputable section

theorem markedMemoryHistory_vertex_anchor_coherence
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
    (hd : MarkedMemoryHistoryBirthDistinct hZ history)
    (r t : Fin (n+1)) (b c : J) (k l : Fin (pads+1))
    (hp : ((markedMemoryHistoryVertexState hZ history r).2.1 b k).1 =
      ((markedMemoryHistoryVertexState hZ history t).2.1 c l).1) :
    markedMemoryPopulationAnchor hZ (markedMemoryHistoryVertexState hZ history r) (Sum.inl ⟨b,k⟩) =
      markedMemoryPopulationAnchor hZ (markedMemoryHistoryVertexState hZ history t) (Sum.inl ⟨c,l⟩) := by
  have hr := markedMemoryHistoryTraceState_stage hZ history (markedMemoryHistoryVertexStage n r)
  have ht := markedMemoryHistoryTraceState_stage hZ history (markedMemoryHistoryVertexStage n t)
  have hp' : markedMemoryPopulationPrime
      (markedMemoryHistoryTraceState hZ history
        (markedMemoryHistoryStageTime (markedMemoryHistoryVertexStage n r))) (Sum.inl ⟨b,k⟩) =
      markedMemoryPopulationPrime
      (markedMemoryHistoryTraceState hZ history
        (markedMemoryHistoryStageTime (markedMemoryHistoryVertexStage n t))) (Sum.inl ⟨c,l⟩) := by
    rw [hr, ht]
    exact hp
  have h := markedMemoryHistory_prime_anchor_coherence ν V hZ ψ η d₀ Y Q ρ qStage χ n j
    history hw hempty hd
    (markedMemoryHistoryStageTime (markedMemoryHistoryVertexStage n r))
    (markedMemoryHistoryStageTime (markedMemoryHistoryVertexStage n t))
    (Sum.inl ⟨b,k⟩) (Sum.inl ⟨c,l⟩) hp'
  rw [hr, ht] at h
  exact h

theorem markedMemoryHistory_vertex_line_coherence
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
    (hd : MarkedMemoryHistoryBirthDistinct hZ history)
    (p : Nat.Primes) (r t : Fin (n+1)) (b c : J) (k l : Fin (pads+1))
    (hr : ((markedMemoryHistoryVertexState hZ history r).2.1 b k).1 = p)
    (ht : ((markedMemoryHistoryVertexState hZ history t).2.1 c l).1 = p) :
    markedPrimePositionLine (p : ℕ) (markedMemoryHistoryVertexState hZ history r).1.1
        (hZ _ (markedMemoryHistoryVertexState hZ history r).1.2) =
      markedPrimePositionLine (p : ℕ) (markedMemoryHistoryVertexState hZ history t).1.1
        (hZ _ (markedMemoryHistoryVertexState hZ history t).1.2) := by
  have h := markedMemoryHistory_vertex_anchor_coherence ν V hZ ψ η d₀ Y Q ρ qStage χ n j
    history hw hempty hd r t b c k l (hr.trans ht.symm)
  change (⟨((markedMemoryHistoryVertexState hZ history r).2.1 b k).1,
      markedPrimePositionLine (((markedMemoryHistoryVertexState hZ history r).2.1 b k).1 : ℕ)
        (markedMemoryHistoryVertexState hZ history r).1.1
        (hZ _ (markedMemoryHistoryVertexState hZ history r).1.2)⟩ : MarkedMemoryAnchoredPrime) =
    ⟨((markedMemoryHistoryVertexState hZ history t).2.1 c l).1,
      markedPrimePositionLine (((markedMemoryHistoryVertexState hZ history t).2.1 c l).1 : ℕ)
        (markedMemoryHistoryVertexState hZ history t).1.1
        (hZ _ (markedMemoryHistoryVertexState hZ history t).1.2)⟩ at h
  rw [hr, ht] at h
  exact (sigma_mk_injective (β := fun q : Nat.Primes => MarkedRawPrimeLine q) (i := p)) h

theorem markedMemoryHistory_active_coherent_of_weight_ne_zero
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
    (hd : MarkedMemoryHistoryBirthDistinct hZ history)
    (p : Nat.Primes) (a : Fin (n+1))
    (ha : a ∈ markedMemoryActiveVisits (fun v => (markedMemoryHistoryVertexState hZ history v).2.1) p) :
    MarkedMemoryActiveCoherent
      (markedMemoryActiveVisits (fun v => (markedMemoryHistoryVertexState hZ history v).2.1) p)
      (fun v => markedPrimePositionLine (p : ℕ) (markedMemoryHistoryVertexState hZ history v).1.1
        (hZ _ (markedMemoryHistoryVertexState hZ history v).1.2)) a := by
  classical
  obtain ⟨c,l,ht⟩ := (Finset.mem_filter.mp ha).2
  intro r hr
  obtain ⟨b,k,hs⟩ := (Finset.mem_filter.mp hr).2
  exact markedMemoryHistory_vertex_line_coherence ν V hZ ψ η d₀ Y Q ρ qStage χ n j
    history hw hempty hd p r a b c k l hs ht

end
end ArtinMatthews
