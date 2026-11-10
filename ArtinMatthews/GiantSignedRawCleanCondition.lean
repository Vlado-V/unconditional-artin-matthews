module

public import ArtinMatthews.GiantSignedAuxiliaryBan
public import ArtinMatthews.GiantSignedRawEdgeSplit
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

/-! On the actual clean choice, the full auxiliary exclusion reduces to
the big-label exclusion by the original cross-band disjointness. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [Fintype (GiantTwoSidedResidueState PS (k+ell))]
    {C : B → Finset (Fin k)}

omit [Fintype B] [DecidableEq S] [DecidableEq B]
  [Fintype (GiantTwoSidedResidueState PS (k+ell))] in
theorem giantSignedRawClean_auxiliary_small
    (hcross : ∀ g j, Disjoint (PB g) (PS j))
    (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2)
    (g : B) (a : C g) (j : S) (i : Fin (k+ell)) :
    (r.auxiliary g a).val ≠ ((giantSignedRawEdgeSmallSource s r).val.2 j i).val ∧
      (r.auxiliary g a).val ≠ (r.smallTarget.val.2 j i).val := by
  have hd := Finset.disjoint_left.mp (hcross g j)
  constructor
  · intro he
    exact hd (r.auxiliary g a).property (he.symm ▸ ((giantSignedRawEdgeSmallSource s r).val.2 j i).property)
  · intro he
    exact hd (r.auxiliary g a).property (he.symm ▸ (r.smallTarget.val.2 j i).property)

omit [DecidableEq S] [DecidableEq B]
  [Fintype (GiantTwoSidedResidueState PS (k+ell))] in
theorem giantSignedRawClean_condition_iff
    (hcross : ∀ g j, Disjoint (PB g) (PS j)) (κ : ℤ)
    (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) (hr : GiantSignedRawEdgeClean r) :
    GiantSignedRawEdgeCondition κ s r ↔
      (∀ g : S, ∀ i : Fin k, r.smallTarget.val.2 g (Fin.castAdd ell i) =
        (giantSignedRawEdgeSmallSource s r).val.2 g (Fin.castAdd ell i)) ∧
      r.smallTarget.val.1 =
        giantTwoSidedResidueTranslate (κ * (giantSignedRawEdgeProduct s r : ℤ))
          (giantSignedRawEdgeSmallSource s r).val.1 ∧
      IdealCopied C (giantSignedRawEdgeBigSource s r) r.bigTarget ∧
      GiantSignedAuxiliaryBan C (giantSignedRawEdgeBigSource s r) r.bigTarget r.auxiliary := by
  constructor
  · rintro ⟨hsmall, hshift, hcopy, _, haux⟩
    refine ⟨hsmall, hshift, hcopy, ?_⟩
    intro g j a i
    exact (haux g a).2 j i
  · rintro ⟨hsmall, hshift, hcopy, haux⟩
    refine ⟨hsmall, hshift, hcopy, ?_, ?_⟩
    · intro g i
      have hzero : (r.choice.1 g).card = 0 := by
        rw [congrFun hr.1 g]
        rfl
      have hi : i.val < 0 := lt_of_lt_of_eq i.isLt hzero
      exact (Nat.not_lt_zero _ hi).elim
    · intro g a
      exact ⟨fun j i => giantSignedRawClean_auxiliary_small hcross s r g a j i,
        fun j i => haux g j a i⟩

end
end ArtinMatthews
