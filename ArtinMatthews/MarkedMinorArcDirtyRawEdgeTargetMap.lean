module

public import ArtinMatthews.MarkedMinorArcDirtyGoodRow
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeChoices
public import ArtinMatthews.MarkedMinorArcRawEdgeDetector
public import ArtinMatthews.MarkedMinorArcRawSlotAverage
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeDeterminant
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeIndices
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeOmissionAverage
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeSlotGeometry
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

/-! Nonzero actual delta edge choices map to the literal counted dirty
omission/target choices, including the actual source slot permutation. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

def markedDirtyRawEdgeTrials {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} (source : MarkedRawActive P M)
    (memory : MarkedRawMemory P B) (I : Finset J) : Finset ℤ := by
  classical
  exact (Finset.univ.product (markedRawPromotionProductSupport memory I)).image
    (fun c : (J → Fin M) × ℕ => ((markedSourceCopiedProduct (markedRawNumericActive source) c.1*c.2:ℕ):ℤ))

theorem markedDirtyRawEdge_source_prime_dvd_full {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M : ℕ} (source : MarkedRawActive P M) (j : J) (k : Fin M) :
    ((source j k).1:ℕ) ∣ markedSourceFullProduct (markedRawNumericActive source) :=
  (Finset.dvd_prod_of_mem (fun l => ((source j l).1:ℕ)) (Finset.mem_univ k)).trans
    (Finset.dvd_prod_of_mem (fun i => ∏ l, ((source i l).1:ℕ)) (Finset.mem_univ j))

theorem markedDirtyRawEdge_delta_target_mem_after_slots {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ η : ℝ → ℂ) (d₀ Y ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z)
    (σ : J → Equiv.Perm (Fin (pads+1)))
    (choice : MarkedRawEdgeChoice hZ (markedRawSlotEquiv σ s))
    (jstar : J) (kstar : Fin (s.2.2.1.1 jstar:ℕ)) (hk : choice.promotions jstar=some kstar)
    (Q : Finset ℤ)
    (hQ : markedDirtyRawEdgeTrials s.2.1 s.2.2
      ((markedDirtyEdgePromotedGroups choice.promotions).erase jstar) ⊆ Q)
    (hne : markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ (markedRawEdgeDeltaDetector ψ Y)
      (markedRawSlotEquiv σ s) choice ≠ 0) :
    ((fun j => σ j (Fin.last pads),markedDirtyEdgeOtherPromotedProduct s.2.2 choice.promotions choice.fresh jstar),
      choice.target) ∈ markedRawDirtyTargetChoices s.2.1 (s.2.2.2 jstar kstar)
        (markedRawPromotionProductSupport s.2.2 ((markedDirtyEdgePromotedGroups choice.promotions).erase jstar))
        Z hZ s.1.1 (markedDirtyEdgeFreshProduct s.2.2 choice.promotions choice.fresh) Q := by
  classical
  let I := (markedDirtyEdgePromotedGroups choice.promotions).erase jstar
  let other := markedDirtyEdgeOtherPromotedProduct s.2.2 choice.promotions choice.fresh jstar
  have hother : other ∈ markedRawPromotionProductSupport s.2.2 I := by
    apply Finset.mem_image.mpr
    exact ⟨markedDirtyEdgeOtherPromotionTuple s.2.2 choice.promotions jstar,Finset.mem_univ _,
      (markedDirtyEdgeOtherPromotedProduct_tuple s.2.2 choice.promotions choice.fresh jstar).symm⟩
  have hs := markedDirtyRawEdge_delta_support hZ ψ η d₀ Y ρ χ (markedRawSlotEquiv σ s) choice hne
  have hban : ¬MarkedRawFullCrossBan s.2.1 (markedRawEdgeTargetLast s.2.2 choice.promotions choice.fresh) := by
    exact (markedDirtyRawStateSlot_crossBan_iff σ s _).not.mp hs.2.2.1
  have hcop := markedDirtyEdgeCrossBan_other_coprime s.2.1 s.2.2 choice.promotions choice.fresh jstar hban
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,hother⟩,Finset.mem_univ _⟩,?_,?_,?_,?_⟩
  · intro j k
    exact ((s.2.1 j k).1.2.coprime_iff_not_dvd).mp
      (hcop.of_dvd_left (markedDirtyRawEdge_source_prime_dvd_full s.2.1 j k))
  · apply hQ
    exact Finset.mem_image.mpr ⟨(fun j => σ j (Fin.last pads),other),
      Finset.mem_product.mpr ⟨Finset.mem_univ _,hother⟩,rfl⟩
  · have hd := markedDirtyRawEdge_delta_determinant hZ ψ η d₀ Y ρ χ (markedRawSlotEquiv σ s) choice jstar kstar hk hne
    rw [markedDirtyRawStateSlot_full_product,markedDirtyRawStateSlot_copied_product] at hd
    exact hd
  · exact choice.promotion_hits jstar kstar hk

end ArtinMatthews
