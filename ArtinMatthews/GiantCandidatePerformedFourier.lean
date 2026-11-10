module

public import ArtinMatthews.GiantSignedJoinedSourceFamily
public import ArtinMatthews.GiantTwoSidedExpandedFourier
public import ArtinMatthews.GiantTwoSidedGroupReindexTransport
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

/-! The exact selected group carrier of the root replacement theorem
has the same signed Fourier moment as its split small/big carrier. -/
namespace ArtinMatthews
noncomputable section

theorem giantCandidatePerformedFourier_eq_split {I : Type*} {x : ℝ}
    (groups : Finset (GiantCandidateGroupIndex x))
    [∀ p : ↥(markedPhysicalBandPrimes (fun j : ↥groups => giantCandidateGroup x j.val)), NeZero p.val]
    [∀ p : ↥(markedPhysicalBandPrimes (Sum.elim (giantCandidatePerformedSmallBand groups)
      (giantCandidatePerformedBigBand groups))), NeZero p.val]
    (hdis : Pairwise (fun i j : ↥groups => Disjoint (giantCandidateGroup x i.val) (giantCandidateGroup x j.val)))
    {k ell n : ℕ} (patterns : Fin n → Finset I)
    (C : Fin n → I → GiantCandidatePerformedBig groups → Finset (Fin k)) (κ : Fin n → ℤ)
    (q : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i p, GiantTwoSidedPatternCoefficient (giantCandidatePerformedBigBand groups) (C i p) ell)
    (θ : AddCircle (1 : ℝ)) :
    giantTwoSidedExpandedIndependentFourierMoment patterns (fun i p => giantCandidatePerformedPattern groups (C i p))
      κ q ζ (fun i p => giantCandidatePerformedCoefficient groups (K i p)) θ =
      giantTwoSidedExpandedIndependentFourierMoment patterns
        (fun i p => giantSignedJoinedPattern (S := GiantCandidatePerformedSmall groups) (C i p)) κ q ζ
        (fun i p => giantSignedJoinedCoefficient (PS := giantCandidatePerformedSmallBand groups) (K i p)) θ := by
  symm
  refine giantTwoSidedExpandedIndependentFourierMoment_reindex (giantCandidatePerformedSplitEquiv groups)
    (giantCandidatePerformedSplit_band groups) hdis patterns _ _
    (fun i p => giantCandidatePerformedSplit_pattern groups (C i p)) κ q ζ _ _ ?_ θ
  intro i p a b z
  rfl

end
end ArtinMatthews
