module

public import ArtinMatthews.MarkedMemoryBoundedHistoryIndex
public import ArtinMatthews.MarkedMemoryActualSlotOrder
public import ArtinMatthews.MarkedMemoryFiniteTableauRestriction
public import ArtinMatthews.MarkedMemoryIndependentRelabel
public import ArtinMatthews.MarkedMemoryActualHistoryReconstruction
public import ArtinMatthews.MarkedMemoryActualIdentityBound
public import ArtinMatthews.MarkedMemoryFiniteHistory
public import ArtinMatthews.MarkedMemoryIndependentRelabelHistory
public import ArtinMatthews.MarkedMemoryTransitionDeterminism
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

/-! Every nonzero actual history lies in one common finite index of
bounded, Fin-labelled independent tableaus. Its exact signed sum may
therefore be restricted to that image without any coverage assumption. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}

abbrev markedMemoryActualLabelBound : ℕ := Fintype.card J*(pads+1)+B+(n+1)*B+n*Fintype.card J

variable (history : MarkedMemoryChronologicalHistory hZ n s)
  (ha : MarkedMemoryHistoryAnchorAdmissible hZ history)

local notation "actual" => markedMemoryActualTableau hZ history ha
local notation "normalized" => markedMemoryIndependentRelabelFin hZ actual
local notation "finiteData" => markedMemoryIndependent_toFinite hZ normalized
local notation "order" => markedMemoryActualOrder hZ history ha

def markedMemoryActualLabelCounts (j : J) : Fin (markedMemoryActualLabelBound (J := J) (pads := pads) (B := B) (n := n)+1) :=
  ⟨Fintype.card (MarkedMemoryActualFiber hZ history j),Nat.lt_succ_of_le (markedMemoryActualFiber_card_le hZ history j)⟩

theorem markedMemoryActualNormalized_initial :
    markedMemoryIndependentState hZ (markedMemoryFiniteTableau_toIndependent hZ finiteData) 0 (Nat.zero_le n) = s :=
  (markedMemoryFinite_restore_state hZ normalized 0 (Nat.zero_le n)).trans
    ((markedMemoryIndependentRelabel_state hZ (fun j => Fintype.equivFin (MarkedMemoryActualFiber hZ history j))
      actual 0 (Nat.zero_le n)).trans (markedMemoryActualTableau_initial hZ history ha))

def markedMemoryActualBoundedIndex :
    MarkedMemoryBoundedHistoryIndex (n := n) hZ s (markedMemoryActualLabelBound (J := J) (pads := pads) (B := B) (n := n)) :=
  ⟨markedMemoryActualLabelCounts hZ history,
    (⟨finiteData,markedMemoryActualNormalized_initial hZ history ha⟩,order)⟩

theorem markedMemoryActualBounded_reconstruction :
    markedMemoryBoundedHistoryAssembly hZ s _ (markedMemoryActualBoundedIndex hZ history ha) = history := by
  have hf := markedMemoryFinite_restore_history_heq hZ normalized order
  have hr := markedMemoryIndependentRelabelFin_history_heq hZ actual order
  have ho : HEq (markedMemoryIndependentHistory hZ actual order) history :=
    (markedMemoryHistoryTransport_heq hZ (markedMemoryActualTableau_initial hZ history ha)
      (markedMemoryIndependentHistory hZ actual order)).symm.trans
        (heq_of_eq (markedMemoryActualHistory_reconstruction hZ history ha))
  exact eq_of_heq ((markedMemoryHistoryTransport_heq hZ (markedMemoryActualNormalized_initial hZ history ha)
    (markedMemoryIndependentHistory hZ (markedMemoryFiniteTableau_toIndependent hZ finiteData) order)).trans
      (hf.trans (hr.trans ho)))

include ha in
theorem markedMemoryActualBounded_covered :
    history ∈ Set.range (markedMemoryBoundedHistoryAssembly (n := n) hZ s
      (markedMemoryActualLabelBound (J := J) (pads := pads) (B := B) (n := n))) :=
  ⟨markedMemoryActualBoundedIndex hZ history ha,markedMemoryActualBounded_reconstruction hZ history ha⟩

variable (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
  (d₀ Y Q ρ : ℝ) (qStage : ℕ → ℝ)
  (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (j : ℕ)

theorem markedMemoryActualBounded_covered_of_weight_ne_zero
    (hw : markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j history ≠ 0) :
    history ∈ Set.range (markedMemoryBoundedHistoryAssembly (n := n) hZ s
      (markedMemoryActualLabelBound (J := J) (pads := pads) (B := B) (n := n))) :=
  markedMemoryActualBounded_covered hZ history
    (markedMemoryHistoryAnchorAdmissible_of_weight_ne_zero ν V hZ ψ η d₀ Y Q ρ qStage χ n j history hw)

/-- Exact original signed weights and arbitrary full-history tests,
including guards and ordered terminal observables, sum over the common
finite tableau image by the proved nonzero-weight coverage. -/
theorem markedMemoryActualBounded_weighted_functional_sum
    (F : MarkedMemoryChronologicalHistory hZ n s → ℂ) :
    (∑ h : MarkedMemoryChronologicalHistory hZ n s,
      markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j h *
        F h) =
    ∑ h : Set.range (markedMemoryBoundedHistoryAssembly (n := n) hZ s
      (markedMemoryActualLabelBound (J := J) (pads := pads) (B := B) (n := n))),
      markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j h.1 *
        F h.1 := by
  let p := fun h : MarkedMemoryChronologicalHistory hZ n s =>
    h ∈ Set.range (markedMemoryBoundedHistoryAssembly (n := n) hZ s
      (markedMemoryActualLabelBound (J := J) (pads := pads) (B := B) (n := n)))
  let f := fun h : MarkedMemoryChronologicalHistory hZ n s =>
    markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j h * F h
  have hz : (∑ h : {h // ¬p h},f h.1) = 0 := by
    apply Finset.sum_eq_zero
    intro h _
    have hw : markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j h.1 = 0 := by
      by_contra hn
      exact h.2 (markedMemoryActualBounded_covered_of_weight_ne_zero hZ h.1 ν V ψ η d₀ Y Q ρ qStage χ j hn)
    exact mul_eq_zero_of_left hw _
  have he := Fintype.sum_subtype_add_sum_subtype p f
  rw [hz,add_zero] at he
  have hirr (i₁ i₂ : Fintype {h : MarkedMemoryChronologicalHistory hZ n s // p h}) :
      @Finset.sum _ ℂ _ (@Finset.univ _ i₁) (fun h => f h.1) =
        @Finset.sum _ ℂ _ (@Finset.univ _ i₂) (fun h => f h.1) := by
    cases Subsingleton.elim i₁ i₂
    rfl
  exact he.symm.trans (hirr _ _)


/-- Terminal observables are the corresponding specialization of the
exact full-history functional identity. -/
theorem markedMemoryActualBounded_weighted_image_sum
    (F : MarkedRawState P (pads+1) B Z → ℂ) :
    (∑ h : MarkedMemoryChronologicalHistory hZ n s,
      markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j h *
        F (markedMemoryChronologicalTarget hZ h)) =
    ∑ h : Set.range (markedMemoryBoundedHistoryAssembly (n := n) hZ s
      (markedMemoryActualLabelBound (J := J) (pads := pads) (B := B) (n := n))),
      markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j h.1 *
        F (markedMemoryChronologicalTarget hZ h.1) :=
  markedMemoryActualBounded_weighted_functional_sum hZ ν V ψ η d₀ Y Q ρ qStage χ j
    (fun h => F (markedMemoryChronologicalTarget hZ h))

end
end ArtinMatthews
