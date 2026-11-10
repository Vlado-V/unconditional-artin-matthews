module

public import ArtinMatthews.MarkedMemoryCanonicalFiber
public import ArtinMatthews.MarkedMemoryActualBoundedHistory
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

/-! One genuine finite index for normalized tableaux on all bounded
particle-count families. Its actual nonzero coverage follows from the
proved identity bound and canonical normalized extraction. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z) (K : ℕ)

abbrev MarkedMemoryNormalizedBoundedIndex :=
  Σ counts : J → Fin (K+1),
    MarkedMemoryNormalizedHistoryIndex (A := fun j => Fin (counts j : ℕ)) (n := n) hZ s

instance markedMemoryNormalizedBoundedIndex_fintype :
    Fintype (MarkedMemoryNormalizedBoundedIndex (n := n) hZ s K) := by infer_instance

def markedMemoryNormalizedBoundedAssembly (i : MarkedMemoryNormalizedBoundedIndex (n := n) hZ s K) :
    MarkedMemoryChronologicalHistory hZ n s := markedMemoryNormalizedHistoryAssembly hZ s i.2

variable (history : MarkedMemoryChronologicalHistory hZ n s)
  (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)

def markedMemoryActualNormalizedBoundedIndex
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history) :
    MarkedMemoryNormalizedBoundedIndex (n := n) hZ s
      (markedMemoryActualLabelBound (J := J) (pads := pads) (B := B) (n := n)) :=
  ⟨markedMemoryActualLabelCounts hZ history,
    markedMemoryCanonicalLabelIndex hZ s history hempty ha
      (fun j => Fintype.equivFin (MarkedMemoryActualFiber hZ history j))⟩

theorem markedMemoryActualNormalizedBounded_reconstruction
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history) :
    markedMemoryNormalizedBoundedAssembly hZ s _
      (markedMemoryActualNormalizedBoundedIndex hZ s history hempty ha)=history :=
  markedMemoryCanonicalLabelIndex_assembly hZ s history hempty ha
    (fun j => Fintype.equivFin (MarkedMemoryActualFiber hZ history j))

include hempty in
theorem markedMemoryActualNormalizedBounded_covered_of_weight_ne_zero
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (offset : ℕ)
    (hw : markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n offset history≠0) :
    history ∈ Set.range (markedMemoryNormalizedBoundedAssembly (n := n) hZ s
      (markedMemoryActualLabelBound (J := J) (pads := pads) (B := B) (n := n))) := by
  let ha := markedMemoryHistoryAnchorAdmissible_of_weight_ne_zero ν V hZ ψ η d₀ Y Q ρ qStage χ n offset history hw
  exact ⟨markedMemoryActualNormalizedBoundedIndex hZ s history hempty ha,
    markedMemoryActualNormalizedBounded_reconstruction hZ s history hempty ha⟩

theorem markedMemoryBoundedCounts_indicator_sum {J : Type*} [Fintype J]
    (K : ℕ) (c : J → ℕ) (hc : ∀ j,c j≤K) (z : ℂ) :
    (∑ N : J → Fin (K+1),if ∀ j,c j=(N j:ℕ) then z else 0)=z := by
  classical
  let N₀ : J → Fin (K+1) := fun j => ⟨c j,Nat.lt_succ_of_le (hc j)⟩
  have he (N : J → Fin (K+1)) : (∀ j,c j=(N j:ℕ)) ↔ N=N₀ := by
    constructor
    · intro h
      funext j
      exact Fin.ext (h j).symm
    · intro h
      subst N
      exact fun _ => rfl
  simp only [he]
  simp

end
end ArtinMatthews
