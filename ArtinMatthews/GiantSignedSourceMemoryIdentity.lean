module

public import ArtinMatthews.GiantSignedCappedBoundaryRank
public import ArtinMatthews.GiantSignedJoinedSourceFamily
public import ArtinMatthews.GiantSignedTiltedLaw
public import ArtinMatthews.GiantTwoSidedExpandedFourier
public import ArtinMatthews.GiantSignedFixedLifespanSourceExpansion
public import ArtinMatthews.GiantSignedSourceTraceLifespanSum
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

/-! The original independent Fourier moment equals the actual signed
birth-distinct chronological boundary times the original big baseline. -/

namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ p : ↥(markedPhysicalBandPrimes PB), NeZero p.val]
    [∀ p : ↥(markedPhysicalBandPrimes (Sum.elim PS PB)), NeZero p.val]

theorem giantTwoSidedExpandedIndependentFourierMoment_eq_signedMemory
    (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (κ : Fin n → ℤ) (q ρ θ : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i p, GiantTwoSidedPatternCoefficient PB (C i p) ell)
    (hP : ∀ (g : S ⊕ B) p, p ∈ Sum.elim PS PB g → p.Prime)
    (hdis : Pairwise (fun i j : S ⊕ B => Disjoint (Sum.elim PS PB i) (Sum.elim PS PB j)))
    (hκ : ∀ i, 0 < (κ i).natAbs)
    (hsize : ∀ i g p, p ∈ Sum.elim PS PB g → (κ i).natAbs < p)
    (hq : 0 < q) (hq1 : q < 1) (hn : 0 < n)
    (hV : ∀ g, bandReciprocalMass (PB g) ≠ 0) (hρ : ρ ≠ 0)
    (hb : ∀ p : ↥(markedPhysicalBandPrimes PB), giantSignedPrimeBaseline (markedMemoryVisitQ q n) p.val ≠ 0) :
    let visitQ := markedMemoryVisitQ q n
    let ν (g : B) := giantSignedTiltedPrimeLaw (PB g) visitQ
    let V (g : B) := bandReciprocalMass (PB g)
    let rows := giantSignedChronologicalTraceRows (PS := PS) ν V q ρ θ n patterns C κ visitQ ζ K (fun _ _ _ _ => 1)
    giantTwoSidedExpandedIndependentFourierMoment patterns
      (fun i p => giantSignedJoinedPattern (C i p)) κ q ζ
      (fun i p => giantSignedJoinedCoefficient (PS := PS) (K i p)) (θ : AddCircle (1 : ℝ)) =
      ((∏ p : ↥(markedPhysicalBandPrimes PB), giantSignedPrimeBaseline visitQ p.val : ℝ) : ℂ) *
        giantSignedGuardedTraceBoundaryPairing (PS := PS) ν rows
          (giantSignedTraceBirthDistinctIndicator ν V q ρ θ n patterns C κ visitQ ζ K (fun _ _ _ _ => 1)) := by
  intro visitQ ν V rows
  exact (giantTwoSidedExpandedIndependentFourierMoment_eq_fixedLifespans patterns C κ q ζ K
      (θ : AddCircle (1 : ℝ)) hdis hb).trans
    (congrArg (fun z : ℂ => ((∏ p : ↥(markedPhysicalBandPrimes PB), giantSignedPrimeBaseline visitQ p.val : ℝ) : ℂ) * z)
      (giantSignedGuardedSourceTraceBoundaryPairing_eq_fixedLifespans patterns C κ q ρ θ ζ K
        hP hdis hκ hsize hq hq1 hn hV hρ hb).symm)

end
end ArtinMatthews
