module

public import ArtinMatthews.MarkedMemoryNormalizedHistoryIndex
public import ArtinMatthews.MarkedMemoryActualHistoryReconstruction
public import ArtinMatthews.MarkedMemoryFiniteHistory
public import ArtinMatthews.MarkedMemoryFiniteLabeling
public import ArtinMatthews.MarkedMemoryIndependentRelabelHistory
public import ArtinMatthews.MarkedMemoryNormalizedFiberExtraction
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

/-! The whole normalized finite assembly fiber is classified by genuine
per-band label equivalences to canonical extraction. Both directions
are constructed; no fiber cardinality or transitivity premise is used. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
  (history : MarkedMemoryChronologicalHistory hZ n s)
  (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)
  (ha : MarkedMemoryHistoryAnchorAdmissible hZ history)

local notation "canonical" => markedMemoryActualTableau hZ history ha
local notation "order" => markedMemoryActualOrder hZ history ha

def markedMemoryCanonicalLabelIndex
    (e : (j : J) → MarkedMemoryActualFiber hZ history j ≃ A j) :
    MarkedMemoryNormalizedHistoryIndex (A := A) (n := n) hZ s :=
  ⟨(⟨markedMemoryIndependent_toFinite hZ (markedMemoryIndependentRelabel hZ e canonical),
      (markedMemoryFinite_restore_state hZ (markedMemoryIndependentRelabel hZ e canonical) 0 (Nat.zero_le n)).trans
        ((markedMemoryIndependentRelabel_state hZ e canonical 0 (Nat.zero_le n)).trans
          (markedMemoryActualTableau_initial hZ history ha))⟩,order),
    (markedMemoryFiniteAnchorNormalize_admissible_fixed_iff hZ _).mpr
      (markedMemoryBirthNormalized_restore hZ _
        (markedMemoryBirthNormalized_relabel hZ canonical
          (markedMemoryActualTableau_birthNormalized hZ history hempty ha) e))⟩

theorem markedMemoryCanonicalLabelIndex_tableau
    (e : (j : J) → MarkedMemoryActualFiber hZ history j ≃ A j) :
    (markedMemoryCanonicalLabelIndex hZ s history hempty ha e).1.1.1=
      markedMemoryIndependent_toFinite hZ (markedMemoryIndependentRelabel hZ e canonical) := rfl

theorem markedMemoryCanonicalLabelIndex_order
    (e : (j : J) → MarkedMemoryActualFiber hZ history j ≃ A j) :
    (markedMemoryCanonicalLabelIndex hZ s history hempty ha e).1.2=order := rfl

theorem markedMemoryCanonicalLabelIndex_assembly
    (e : (j : J) → MarkedMemoryActualFiber hZ history j ≃ A j) :
    markedMemoryNormalizedHistoryAssembly hZ s (markedMemoryCanonicalLabelIndex hZ s history hempty ha e)=history := by
  have hold : HEq (markedMemoryIndependentHistory hZ canonical order) history :=
    (markedMemoryHistoryTransport_heq hZ (markedMemoryActualTableau_initial hZ history ha) _).symm.trans
      (heq_of_eq (markedMemoryActualHistory_reconstruction hZ history ha))
  apply eq_of_heq
  exact (markedMemoryHistoryTransport_heq hZ
      (markedMemoryCanonicalLabelIndex hZ s history hempty ha e).1.1.2 _).trans
    ((markedMemoryFinite_restore_history_heq hZ (markedMemoryIndependentRelabel hZ e canonical) order).trans
      ((markedMemoryIndependentRelabel_history_heq hZ e canonical order).trans hold))

theorem markedMemoryCanonicalLabelIndex_injective :
    Function.Injective (markedMemoryCanonicalLabelIndex (A := A) hZ s history hempty ha) := by
  intro e f h
  apply markedMemoryFinite_labeling_injective hZ canonical
  exact congrArg (fun i : MarkedMemoryNormalizedHistoryIndex (A := A) (n := n) hZ s => i.1.1.1) h

def markedMemoryCanonicalLabelFiber
    (e : (j : J) → MarkedMemoryActualFiber hZ history j ≃ A j) :
    {i : MarkedMemoryNormalizedHistoryIndex (A := A) (n := n) hZ s //
      markedMemoryNormalizedHistoryAssembly hZ s i=history} :=
  ⟨markedMemoryCanonicalLabelIndex hZ s history hempty ha e,
    markedMemoryCanonicalLabelIndex_assembly hZ s history hempty ha e⟩

theorem markedMemoryCanonicalLabelFiber_injective :
    Function.Injective (markedMemoryCanonicalLabelFiber (A := A) hZ s history hempty ha) := by
  intro e f h
  exact markedMemoryCanonicalLabelIndex_injective hZ s history hempty ha (congrArg Subtype.val h)

theorem markedMemoryCanonicalLabelFiber_surjective :
    Function.Surjective (markedMemoryCanonicalLabelFiber (A := A) hZ s history hempty ha) := by
  intro i
  obtain ⟨e,hf,ho⟩ := markedMemoryNormalizedFiber_extraction hZ s history hempty ha i.1 i.2
  refine ⟨e,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact hf
  · exact ho

def markedMemoryCanonicalFiberEquiv :
    ((j : J) → MarkedMemoryActualFiber hZ history j ≃ A j) ≃
      {i : MarkedMemoryNormalizedHistoryIndex (A := A) (n := n) hZ s //
        markedMemoryNormalizedHistoryAssembly hZ s i=history} :=
  Equiv.ofBijective (markedMemoryCanonicalLabelFiber hZ s history hempty ha)
    ⟨markedMemoryCanonicalLabelFiber_injective hZ s history hempty ha,
      markedMemoryCanonicalLabelFiber_surjective hZ s history hempty ha⟩

end
end ArtinMatthews
