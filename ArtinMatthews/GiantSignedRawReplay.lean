module

public import ArtinMatthews.GiantSignedChronologicalEdge
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

/-! Recover the same raw move from its chronological source and target.
The old-index choice is transported only across the exact memory equality. -/
namespace ArtinMatthews
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}

private theorem giantSignedRawEdgeMove_heq {C : B → Finset (Fin k)} {m m' : GiantSignedMemory PB}
    (hm : m = m') (r : GiantSignedRawEdgeMove PS PB ell C m) (r' : GiantSignedRawEdgeMove PS PB ell C m')
    (hπS : r.sourceSmallPermutation = r'.sourceSmallPermutation)
    (hπB : r.sourceBigPermutation = r'.sourceBigPermutation)
    (hτS : r.targetSmallPermutation = r'.targetSmallPermutation)
    (hτB : r.targetBigPermutation = r'.targetBigPermutation)
    (haux : r.auxiliary = r'.auxiliary) (hc : HEq r.choice r'.choice)
    (hs : r.smallTarget = r'.smallTarget) (hb : r.bigTarget = r'.bigTarget) : HEq r r' := by
  subst m'
  have hchoice := eq_of_heq hc
  cases r
  cases r'
  dsimp only at hπS hπB hτS hτB haux hchoice hs hb
  cases hπS
  cases hπB
  cases hτS
  cases hτB
  cases haux
  cases hchoice
  cases hs
  cases hb
  rfl

theorem giantSignedChronologicalRawMove_replay (κ : ℤ)
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (i : Fin n)
    (s : GiantSignedState PS PB (k+ell)) (r : GiantSignedRawEdgeMove PS PB ell (C i) s.2.2)
    (hs : giantSignedChronologicalAfterVisitState h i.castSucc = s)
    (ht : h.state i.succ = giantSignedRawEdgeTarget κ s r)
    (hπS : h.sourceSmallPermutation i = r.sourceSmallPermutation)
    (hπB : h.sourceBigPermutation i = r.sourceBigPermutation)
    (hτS : h.targetSmallPermutation i = r.targetSmallPermutation)
    (hτB : h.targetBigPermutation i = r.targetBigPermutation)
    (haux : h.auxiliary i = r.auxiliary) (hc : HEq (h.edge i) r.choice) :
    HEq (giantSignedChronologicalRawMove h i) r := by
  refine giantSignedRawEdgeMove_heq
    (congrArg (fun s : GiantSignedState PS PB (k+ell) => s.2.2) hs) _ r
    hπS hπB hτS hτB haux hc ?_ ?_
  · change giantTwoSidedResiduePermute (h.targetSmallPermutation i) (h.state i.succ).1 = _
    rw [hτS, ht]
    exact (giantTwoSidedResiduePermute r.targetSmallPermutation).apply_symm_apply _
  · change giantSignedGroupedTuplePermutation (h.targetBigPermutation i) (h.state i.succ).2.1 = _
    rw [hτB, ht]
    exact (giantSignedGroupedTuplePermutation r.targetBigPermutation).apply_symm_apply _

theorem giantSignedRawEdgeTarget_replay {C : B → Finset (Fin k)} (κ : ℤ)
    {s s' : GiantSignedState PS PB (k+ell)} (hs : s = s')
    {r : GiantSignedRawEdgeMove PS PB ell C s.2.2} {r' : GiantSignedRawEdgeMove PS PB ell C s'.2.2}
    (hr : HEq r r') :
    giantSignedRawEdgeTarget κ s r = giantSignedRawEdgeTarget κ s' r' := by
  subst s'
  cases eq_of_heq hr
  rfl

theorem giantSignedRawEdgeCondition_replay {C : B → Finset (Fin k)} (κ : ℤ)
    {s s' : GiantSignedState PS PB (k+ell)} (hs : s = s')
    {r : GiantSignedRawEdgeMove PS PB ell C s.2.2} {r' : GiantSignedRawEdgeMove PS PB ell C s'.2.2}
    (hr : HEq r r') :
    GiantSignedRawEdgeCondition κ s r ↔ GiantSignedRawEdgeCondition κ s' r' := by
  subst s'
  cases eq_of_heq hr
  rfl

theorem giantSignedRawEdgeCoefficient_replay {C : B → Finset (Fin k)}
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell)
    {s s' : GiantSignedState PS PB (k+ell)} (hs : s = s')
    {r : GiantSignedRawEdgeMove PS PB ell C s.2.2} {r' : GiantSignedRawEdgeMove PS PB ell C s'.2.2}
    (hr : HEq r r') :
    giantSignedRawEdgeCoefficient ν V κ q ρ θ ζ K s r =
      giantSignedRawEdgeCoefficient ν V κ q ρ θ ζ K s' r' := by
  subst s'
  cases eq_of_heq hr
  rfl

end
end ArtinMatthews
