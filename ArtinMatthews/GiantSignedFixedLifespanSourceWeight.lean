module

public import ArtinMatthews.GiantSignedFixedOrderedLifespan
public import ArtinMatthews.GiantSignedJoinedSourceFamily
public import ArtinMatthews.GiantSignedJoinedBigLifespan
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

/-! The original scalar on a fixed guarded path and its supported big
lifespans, before the ordered birth multiplicities are introduced. -/

namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {κ : Fin n → ℤ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

def giantSignedFixedLifespanSourceWeight
    (path : GiantSignedLifespanOriginalPath PS PB (ell := ell) C κ)
    (q : ℝ) (ζ : Fin n → ℝ) (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (θ : AddCircle (1 : ℝ)) (c : GiantSignedFixedLifespanChoices path (markedMemoryVisitQ q n)) : ℂ :=
  ((giantTwoSidedResidueSlotNormalization (J := S ⊕ B) (k+ell) : ℂ)^n) *
    giantTwoSidedRootScalar (giantSignedChronologicalJoinedPattern C) path.labels
      path.sourcePermutation path.targetPermutation path.auxiliary ζ
      (fun i => giantSignedJoinedCoefficient (PS := PS) (K i)) *
    ((giantTwoSidedIndependentResidueFactor PS (giantSignedSmallMarking path.labels) q path.offset
      path.smallRoot / Fintype.card (GiantTwoSidedFullResidue PS) : ℝ) : ℂ) *
    fourier (path.offset (Fin.last n)) θ *
    (giantSignedJoinedBigLifespanNormalizedProduct path.labels path.offset (markedMemoryVisitQ q n) c.val : ℂ)

end
end ArtinMatthews
