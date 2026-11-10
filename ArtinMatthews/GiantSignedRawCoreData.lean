module

public import ArtinMatthews.GiantSignedSmallFreeEdgeData
public import ArtinMatthews.GiantSignedPatternFiberEnergy
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

/-! The canonical full-state core and its exact copied-label fibers. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    {C : B → Finset (Fin k)}

def giantSignedRawCoreApply (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (κ : ℤ) (q ρ : ℝ) (aux : GiantTwoSidedPatternAuxiliary PB C)
    (f : GiantSignedState PS PB (k+ell) → ℂ) (s : GiantSignedState PS PB (k+ell)) : ℂ :=
  giantSignedSmallFreeEdgeApply ν V κ q ρ
    (giantTwoSidedPatternCopiedProduct C s.2.1 * giantTwoSidedPatternAuxiliaryProduct aux)
    (fun z a m => f (z, giantSignedPatternFill C s.2.1 a, m))
    s.1 (giantSignedPatternFreeLabels C s.2.1) s.2.2

theorem giantSignedRawCoreApply_sourceFill
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : ℤ) (q ρ : ℝ)
    (aux : GiantTwoSidedPatternAuxiliary PB C)
    (f : GiantSignedState PS PB (k+ell) → ℂ)
    (c : GiantSignedPatternCopiedLabels PB C)
    (s : GiantTwoSidedResidueState PS (k+ell))
    (a : GiantSignedPrimeTuple PB (fun g => ell + (C g).card)) (m : GiantSignedMemory PB) :
    giantSignedRawCoreApply ν V κ q ρ aux f (s, giantSignedPatternSourceFill C c a, m) =
      giantSignedSmallFreeEdgeApply ν V κ q ρ
        (giantSignedCopiedLabelsProduct c * giantTwoSidedPatternAuxiliaryProduct aux)
        (fun z b out => f (z, giantSignedPatternSourceFill C c b, out)) s a m := by
  simp only [giantSignedRawCoreApply, giantSignedPatternSourceFill_product,
    giantSignedPatternSourceFill_freeLabels, giantSignedPatternSourceFill_patternFill]


end
end ArtinMatthews
