module

public import ArtinMatthews.MarkedMemoryNormalizedHistoryIndex
public import ArtinMatthews.MarkedMemoryFiniteTableauInjective
public import ArtinMatthews.MarkedMemoryNormalizedReverseExtraction
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

/-! Every actual normalized fiber member is a genuine relabeling of
canonical extraction. The finite wrapper removes unused time tails;
the birth-anchor convention removes unused static-anchor freedom. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
  (history : MarkedMemoryChronologicalHistory hZ n s)

theorem markedMemoryNormalizedFiber_extraction
    (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history)
    (i : MarkedMemoryNormalizedHistoryIndex (A := A) (n := n) hZ s)
    (hi : markedMemoryNormalizedHistoryAssembly hZ s i=history) :
    ∃ e : (j : J) → MarkedMemoryActualFiber hZ history j ≃ A j,
      markedMemoryIndependent_toFinite hZ (markedMemoryIndependentRelabel hZ e
        (markedMemoryActualTableau hZ history ha))=i.1.1.1 ∧
          markedMemoryActualOrder hZ history ha=i.1.2 := by
  rcases i with ⟨⟨⟨f,hs⟩,order⟩,hn⟩
  let d := markedMemoryFiniteTableau_toIndependent hZ f
  have hdn : MarkedMemoryBirthNormalized hZ d :=
    (markedMemoryFiniteAnchorNormalize_admissible_fixed_iff hZ f).mp hn
  change markedMemoryIndependentState hZ d 0 (Nat.zero_le n)=s at hs
  cases hs
  change markedMemoryIndependentHistory hZ d order=history at hi
  subst history
  refine ⟨markedMemoryBandAddressEquiv hZ d order,?_,?_⟩
  · exact (markedMemoryNormalized_reverse_extraction hZ d order hempty hdn ha).trans
      (markedMemoryFiniteTableau_restrict_extend hZ f)
  · exact markedMemoryNormalized_reverse_order hZ d order hempty hdn ha

end
end ArtinMatthews
