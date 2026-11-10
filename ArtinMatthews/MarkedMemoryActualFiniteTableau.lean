module

public import ArtinMatthews.MarkedMemoryFiniteHistoryIndex
public import ArtinMatthews.MarkedMemoryActualSlotOrder
public import ArtinMatthews.MarkedMemoryFiniteTableauRestriction
public import ArtinMatthews.MarkedMemoryActualHistoryReconstruction
public import ArtinMatthews.MarkedMemoryFiniteHistory
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

/-! A nonzero actual history lies in the image of a genuine finite
independent-tableau index. The finite data store no original history;
coverage follows from the proved finite roundtrip and literal recovery. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s)
  (ha : MarkedMemoryHistoryAnchorAdmissible hZ history)

local notation "tableau" => markedMemoryActualTableau hZ history ha
local notation "order" => markedMemoryActualOrder hZ history ha

def markedMemoryActualFiniteTableau :
    MarkedMemoryFiniteTableau (A := MarkedMemoryActualFiber hZ history)
      (P := P) (pads := pads) (B := B) hZ n :=
  markedMemoryIndependent_toFinite hZ tableau

theorem markedMemoryActualFinite_initial :
    markedMemoryIndependentState hZ
      (markedMemoryFiniteTableau_toIndependent hZ (markedMemoryActualFiniteTableau hZ history ha))
      0 (Nat.zero_le n) = s :=
  (markedMemoryFinite_restore_state hZ tableau 0 (Nat.zero_le n)).trans
    (markedMemoryActualTableau_initial hZ history ha)

def markedMemoryActualFiniteIndex :
    MarkedMemoryFiniteHistoryIndex (A := MarkedMemoryActualFiber hZ history) (n := n) hZ s :=
  (⟨markedMemoryActualFiniteTableau hZ history ha,markedMemoryActualFinite_initial hZ history ha⟩,order)

theorem markedMemoryActualFinite_reconstruction :
    markedMemoryFiniteHistoryAssembly hZ s (markedMemoryActualFiniteIndex hZ history ha) = history := by
  have hrestore := markedMemoryFinite_restore_history_heq hZ tableau order
  have hold : HEq (markedMemoryIndependentHistory hZ tableau order) history :=
    (markedMemoryHistoryTransport_heq hZ (markedMemoryActualTableau_initial hZ history ha)
      (markedMemoryIndependentHistory hZ tableau order)).symm.trans
        (heq_of_eq (markedMemoryActualHistory_reconstruction hZ history ha))
  exact eq_of_heq ((markedMemoryHistoryTransport_heq hZ (markedMemoryActualFinite_initial hZ history ha)
    (markedMemoryIndependentHistory hZ
      (markedMemoryFiniteTableau_toIndependent hZ (markedMemoryActualFiniteTableau hZ history ha)) order)).trans
      (hrestore.trans hold))

include ha in
theorem markedMemoryActualFinite_covered :
    history ∈ Set.range (markedMemoryFiniteHistoryAssembly (A := MarkedMemoryActualFiber hZ history) (n := n) hZ s) :=
  ⟨markedMemoryActualFiniteIndex hZ history ha,markedMemoryActualFinite_reconstruction hZ history ha⟩

theorem markedMemoryActualFinite_exists_of_weight_ne_zero
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (j : ℕ)
    (hw : markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j history ≠ 0) :
    ∃ index : MarkedMemoryFiniteHistoryIndex (A := MarkedMemoryActualFiber hZ history) (n := n) hZ s,
      markedMemoryFiniteHistoryAssembly hZ s index = history := by
  let hadm := markedMemoryHistoryAnchorAdmissible_of_weight_ne_zero ν V hZ ψ η d₀ Y Q ρ qStage χ n j history hw
  exact ⟨markedMemoryActualFiniteIndex hZ history hadm,markedMemoryActualFinite_reconstruction hZ history hadm⟩

end
end ArtinMatthews
