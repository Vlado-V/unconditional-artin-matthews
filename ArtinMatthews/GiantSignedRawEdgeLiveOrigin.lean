module

public import ArtinMatthews.GiantSignedRawEdgeData
public import ArtinMatthews.GiantSignedEdgeLiveIndices
public import ArtinMatthews.GiantSignedGhostMemoryCoordinates
public import ArtinMatthews.GiantSignedEdgeLivePrime
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

/-! Actual target indices first undo the target slot permutation.
Old active origins then pass through the actual source permutation. -/
namespace ArtinMatthews
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ} {C : B → Finset (Fin k)}
    (κ : ℤ) (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) (g : B)

def giantSignedRawEdgeLiveOrigin :
    GiantSignedLiveSlots (k+ell) ((giantSignedRawEdgeTarget κ s r).2.2.1 g) ↪
      (GiantSignedLiveSlots (k+ell) (s.2.2.1 g) ⊕
        {i : Fin (ell+(C g).card) // i ∉ r.choice.2.1 g}) :=
  ((Equiv.sumCongr (r.targetBigPermutation g).symm (Equiv.refl _)).toEmbedding.trans
    (giantSignedEdgeLiveOrigin (C g) (r.choice.1 g) (r.choice.2.1 g) (r.choice.2.2 g))).trans
      (Equiv.sumCongr
        (Equiv.sumCongr (r.sourceBigPermutation g) (Equiv.refl _)) (Equiv.refl _)).toEmbedding

theorem giantSignedRawEdgeLiveOrigin_prime (hc : GiantSignedRawEdgeCondition κ s r)
    (hh : GiantSignedEdgeHits (κ * (giantSignedRawEdgeProduct s r : ℤ)) s.2.2
      (giantSignedPatternFreeLabels C r.bigTarget) r.choice)
    (z : GiantSignedLiveSlots (k+ell) ((giantSignedRawEdgeTarget κ s r).2.2.1 g)) :
    giantSignedLivePrime ((giantSignedRawEdgeTarget κ s r).2.1 g)
        (giantSignedMemoryGroupEquiv PB (giantSignedRawEdgeTarget κ s r).2.2 g) z =
      Sum.elim (giantSignedLivePrime (s.2.1 g) (giantSignedMemoryGroupEquiv PB s.2.2 g))
        (fun i : {i : Fin (ell+(C g).card) // i ∉ r.choice.2.1 g} =>
          giantSignedPatternFreeLabels C r.bigTarget g i.val)
        (giantSignedRawEdgeLiveOrigin κ s r g z) := by
  let u := Sum.map (r.targetBigPermutation g).symm id z
  let w := giantSignedEdgeLiveOrigin (C g) (r.choice.1 g) (r.choice.2.1 g) (r.choice.2.2 g) u
  have he := giantSignedEdgeLiveOrigin_prime C s.2.2 (giantSignedRawEdgeBigSource s r) r.bigTarget
    r.choice (κ * (giantSignedRawEdgeProduct s r : ℤ)) hc.2.2.1 hh g u
  have hl : giantSignedLivePrime ((giantSignedRawEdgeTarget κ s r).2.1 g)
      (giantSignedMemoryGroupEquiv PB (giantSignedRawEdgeTarget κ s r).2.2 g) z =
      giantSignedLivePrime (r.bigTarget g)
        (giantSignedMemoryGroupEquiv PB (giantSignedRawEdgeTarget κ s r).2.2 g) u := by
    cases z <;> rfl
  refine hl.trans (he.trans ?_)
  change Sum.elim (giantSignedLivePrime ((giantSignedRawEdgeBigSource s r) g)
      (giantSignedMemoryGroupEquiv PB s.2.2 g)) _ w =
    Sum.elim (giantSignedLivePrime (s.2.1 g) (giantSignedMemoryGroupEquiv PB s.2.2 g)) _
      (Sum.map (Sum.map (r.sourceBigPermutation g) id) id w)
  rcases w with (i | i) | i <;> rfl

end
end ArtinMatthews
