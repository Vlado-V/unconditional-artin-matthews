module

public import ArtinMatthews.MarkedMemoryDecoratedLifespans
public import ArtinMatthews.MarkedMemoryLifespanEdgeRecognition
public import ArtinMatthews.MarkedMemoryLifespanSurvival
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

/-! In admissible decorated lifespan data, death/store/promotion decisions
are forced by the supplied intervals and injected identities. The retained
event coordinates cannot independently change those decisions. -/
namespace ArtinMatthews
noncomputable section

universe u w
variable {J : Type u} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} {A : Type w}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)

theorem markedMemoryLifespanRun_source_survives
    (d : MarkedMemoryLifespanRunData hZ s (n := n) A) (t : ℕ) (ht : t < 2*n+1)
    (old : MarkedMemoryHistoryTracePopulation hZ (markedMemoryLifespanRunReconstruct hZ s d) t) :
    Sum.inl old ∈ Set.range (markedMemoryHistoryTraceStep hZ (markedMemoryLifespanRunReconstruct hZ s d) t) ↔
      t < d.last (d.ids t old) := by
  rw [markedMemoryHistory_source_survives_iff_last hZ (markedMemoryLifespanRunReconstruct hZ s d) t ht]
  rw [markedMemoryLifespanRunAddressEquiv_last, markedMemoryLifespanRunAddressEquiv_origin]

theorem markedMemoryLifespanRun_source_dies
    (d : MarkedMemoryLifespanRunData hZ s (n := n) A) (t : ℕ) (ht : t < 2*n+1)
    (old : MarkedMemoryHistoryTracePopulation hZ (markedMemoryLifespanRunReconstruct hZ s d) t) :
    Sum.inl old ∉ Set.range (markedMemoryHistoryTraceStep hZ (markedMemoryLifespanRunReconstruct hZ s d) t) ↔
      d.last (d.ids t old) = t := by
  rw [markedMemoryHistory_source_dies_iff_last hZ (markedMemoryLifespanRunReconstruct hZ s d) t ht]
  rw [markedMemoryLifespanRunAddressEquiv_last, markedMemoryLifespanRunAddressEquiv_origin]

theorem markedMemoryLifespanRun_head_ghost_deleted
    (d : MarkedMemoryLifespanRunData hZ s (n := n) A) (j : J) (k : Fin (s.2.2.1.1 j : ℕ)) :
    k ∈ (markedMemoryHistoryHeadGhost hZ (markedMemoryLifespanRunReconstruct hZ s d)).deletion j ↔
      d.last (d.ids 0 (Sum.inr ⟨j,k⟩)) = 0 := by
  rw [markedMemoryHistory_head_ghost_deleted_iff_last, markedMemoryLifespanRunAddressEquiv_last]
  have he := markedMemoryLifespanRunAddressEquiv_origin hZ s d 0 (Sum.inr ⟨j,k⟩)
  change markedMemoryLifespanRunAddressEquiv hZ s d (Sum.inl (Sum.inr ⟨j,k⟩)) =
    d.ids 0 (Sum.inr ⟨j,k⟩) at he
  rw [he]

theorem markedMemoryLifespanRun_first_edge_stored
    (d : MarkedMemoryLifespanRunData hZ s (n := n+1) A) (j : J) :
    (markedMemoryLifespanRunReconstruct hZ s d).2.1.2.1.store j = true ↔
      1 < d.last (d.ids 1 (Sum.inl
        ⟨j,(markedMemoryLifespanRunReconstruct hZ s d).2.1.1 j (Fin.last pads)⟩)) := by
  rw [markedMemoryHistory_first_edge_store_iff, markedMemoryLifespanRunAddressEquiv_last]
  unfold markedMemoryHistoryFirstEdgeSourceLast
  rw [markedMemoryLifespanRunAddressEquiv_origin]

  rfl

theorem markedMemoryLifespanRun_first_edge_promoted
    (d : MarkedMemoryLifespanRunData hZ s (n := n+1) A) (j : J)
    (k : Fin ((markedMemoryGhostChoiceTarget hZ s (markedMemoryLifespanRunReconstruct hZ s d).1).2.2.1.1 j : ℕ)) :
    (markedMemoryLifespanRunReconstruct hZ s d).2.1.2.1.promotions j = some k ↔
      d.ids 1 (Sum.inr ⟨j,k⟩) = d.ids 2 (Sum.inl
        ⟨j,((markedMemoryLifespanRunReconstruct hZ s d).2.1.2.2 j).symm (Fin.last pads)⟩) := by
  let h := markedMemoryLifespanRunReconstruct hZ s d
  let e := markedMemoryLifespanRunAddressEquiv hZ s d
  have h₁ : e (markedMemoryHistoryFirstEdgePending hZ h j k) = d.ids 1 (Sum.inr ⟨j,k⟩) :=
    markedMemoryLifespanRunAddressEquiv_origin hZ s d 1 (Sum.inr ⟨j,k⟩)
  have h₂ : e (markedMemoryHistoryFirstEdgeTargetLast hZ h j) =
      d.ids 2 (Sum.inl ⟨j,(h.2.1.2.2 j).symm (Fin.last pads)⟩) :=
    markedMemoryLifespanRunAddressEquiv_origin hZ s d 2 (Sum.inl ⟨j,(h.2.1.2.2 j).symm (Fin.last pads)⟩)
  calc
    _ ↔ markedMemoryHistoryFirstEdgePending hZ h j k = markedMemoryHistoryFirstEdgeTargetLast hZ h j :=
      markedMemoryHistory_first_edge_promote_iff hZ h j k
    _ ↔ e (markedMemoryHistoryFirstEdgePending hZ h j k) = e (markedMemoryHistoryFirstEdgeTargetLast hZ h j) :=
      e.injective.eq_iff.symm
    _ ↔ _ := by rw [h₁,h₂]

end
end ArtinMatthews
