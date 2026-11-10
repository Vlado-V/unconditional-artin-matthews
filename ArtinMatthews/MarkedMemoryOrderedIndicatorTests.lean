module

public import ArtinMatthews.MarkedMemoryStageTests
public import ArtinMatthews.MarkedMemoryHistoryEdgeAccess
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Ordered zero-one endpoint tests retain their actual source and target
arguments. Ghost and slot invariance are used only to identify those
arguments with the genuine chronological vertex states. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem orderedIndicator_congr {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) :
    (if P then (1:ℂ) else 0)=(if Q then 1 else 0) := by
  by_cases hp : P
  · rw [ite_eq_left hp,ite_eq_left (h.mp hp)]
  · rw [ite_eq_right hp,ite_eq_right (fun hq => hp (h.mpr hq))]

private theorem orderedIndicator_three (P Q R : Prop) [Decidable P] [Decidable Q] [Decidable R] [Decidable (P ∧ Q ∧ R)] :
    (if P then (1:ℂ) else 0)*(if Q then 1 else 0)*(if R then 1 else 0)=
      if P ∧ Q ∧ R then 1 else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;> simp [hP,hQ,hR]

private theorem orderedIndicator_star (P : Prop) [Decidable P] :
    star (if P then (1:ℂ) else 0)=(if P then 1 else 0) := by
  by_cases h : P
  · rw [ite_eq_left h,star_one]
  · rw [ite_eq_right h,star_zero]

variable {J : Type*} [Fintype J]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
  (G : MarkedRawState P (pads+1) B Z → Prop)

def MarkedMemoryOrderedEndpointGuard :
    (n : ℕ) → {s : MarkedRawState P (pads+1) B Z} →
      MarkedMemoryChronologicalHistory hZ n s → Prop
  | 0,_,_ => True
  | n+1,s,H => G s ∧
      G (markedMemoryEdgeChoiceTarget hZ (markedMemoryGhostChoiceTarget hZ s H.1) H.2.1) ∧
      MarkedMemoryOrderedEndpointGuard n H.2.2

theorem markedMemoryOrderedEndpointGuard_vertices
    (n : ℕ) (hn : 0<n) {s : MarkedRawState P (pads+1) B Z}
    (H : MarkedMemoryChronologicalHistory hZ n s) :
    MarkedMemoryOrderedEndpointGuard hZ G n H ↔
      ∀ v : Fin (n+1),G (markedMemoryHistoryVertexState hZ H v) := by
  cases n with
  | zero => omega
  | succ n =>
    clear hn
    induction n generalizing s with
    | zero =>
      simp only [Fin.forall_fin_succ,Fin.forall_fin_zero,and_true]
      change (G s ∧ G (markedMemoryEdgeChoiceTarget hZ
        (markedMemoryGhostChoiceTarget hZ s H.1) H.2.1) ∧ True) ↔
        G s ∧ G (markedMemoryEdgeChoiceTarget hZ
          (markedMemoryGhostChoiceTarget hZ s H.1) H.2.1)
      simp only [and_true]
    | succ n ih =>
      change (G s ∧ G (markedMemoryEdgeChoiceTarget hZ
        (markedMemoryGhostChoiceTarget hZ s H.1) H.2.1) ∧
        MarkedMemoryOrderedEndpointGuard hZ G (n+1) H.2.2) ↔ _
      rw [ih H.2.2]
      conv_rhs => rw [Fin.forall_fin_succ]
      change (G s ∧ G (markedMemoryEdgeChoiceTarget hZ
        (markedMemoryGhostChoiceTarget hZ s H.1) H.2.1) ∧
        (∀ v : Fin (n+2),G (markedMemoryHistoryVertexState hZ H.2.2 v))) ↔
        G s ∧ (∀ v : Fin (n+2),G (markedMemoryHistoryVertexState hZ H.2.2 v))
      constructor
      · exact fun h => ⟨h.1,h.2.2⟩
      · intro h
        exact ⟨h.1,by simpa only [markedMemoryHistoryVertexState_zero] using h.2 0,h.2⟩

theorem markedMemoryStageTestProduct_indicator_guard
    (hghost : ∀ (s : MarkedRawState P (pads+1) B Z) (g : MarkedMemoryGhostChoice hZ s),
      G (markedMemoryGhostChoiceTarget hZ s g) ↔ G s)
    (hslots : ∀ (s : MarkedRawState P (pads+1) B Z)
      (σ : J → Equiv.Perm (Fin (pads+1))),G (markedRawSlotEquiv σ s) ↔ G s)
    (n offset : ℕ) {s : MarkedRawState P (pads+1) B Z}
    (H : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryStageTestProduct hZ (fun _ u => if G u then 1 else 0) n offset H=
      if MarkedMemoryOrderedEndpointGuard hZ G n H then 1 else 0 := by
  induction n generalizing s offset with
  | zero => exact (ite_eq_left trivial).symm
  | succ n ih =>
    have hs : G (markedRawSlotEquiv H.2.1.1 (markedMemoryGhostChoiceTarget hZ s H.1)) ↔ G s :=
      (hslots _ _).trans (hghost s H.1)
    have ht : G (markedRawEdgeTargetState hZ
        (markedRawSlotEquiv H.2.1.1 (markedMemoryGhostChoiceTarget hZ s H.1)) H.2.1.2.1) ↔
        G (markedMemoryEdgeChoiceTarget hZ (markedMemoryGhostChoiceTarget hZ s H.1) H.2.1) :=
      (hslots _ H.2.1.2.2).symm
    rw [markedMemoryStageTestProduct,orderedIndicator_congr hs,orderedIndicator_congr ht,ih]
    exact @orderedIndicator_three (G s)
      (G (markedMemoryEdgeChoiceTarget hZ (markedMemoryGhostChoiceTarget hZ s H.1) H.2.1))
      (MarkedMemoryOrderedEndpointGuard hZ G n H.2.2)
      (Classical.propDecidable _) (Classical.propDecidable _)
      (Classical.propDecidable _) (Classical.propDecidable _)

theorem markedMemoryStageTestProduct_oriented_indicator
    (hghost : ∀ (s : MarkedRawState P (pads+1) B Z) (g : MarkedMemoryGhostChoice hZ s),
      G (markedMemoryGhostChoiceTarget hZ s g) ↔ G s)
    (hslots : ∀ (s : MarkedRawState P (pads+1) B Z)
      (σ : J → Equiv.Perm (Fin (pads+1))),G (markedRawSlotEquiv σ s) ↔ G s)
    (orientation : ℕ → Bool) (n offset : ℕ) (hn : 0<n)
    {s : MarkedRawState P (pads+1) B Z} (H : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryStageTestProduct hZ
      (fun k => if orientation k then fun u => star (if G u then (1:ℂ) else 0)
        else fun u => if G u then 1 else 0) n offset H=
      if ∀ v : Fin (n+1),G (markedMemoryHistoryVertexState hZ H v) then 1 else 0 := by
  have ho : (fun k => if orientation k then fun u => star (if G u then (1:ℂ) else 0)
      else fun u => if G u then 1 else 0)=(fun _ u => if G u then 1 else 0) := by
    funext k u
    by_cases hk : orientation k=true
    · rw [ite_eq_left hk]
      exact orderedIndicator_star _
    · rw [ite_eq_right hk]
  rw [ho,markedMemoryStageTestProduct_indicator_guard hZ G hghost hslots]
  exact orderedIndicator_congr (markedMemoryOrderedEndpointGuard_vertices hZ G n hn H)

end
end ArtinMatthews
