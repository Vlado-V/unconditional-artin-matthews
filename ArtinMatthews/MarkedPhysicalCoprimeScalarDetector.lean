module

public import ArtinMatthews.MarkedPhysicalScalarDetector
public import ArtinMatthews.MarkedMajorLabelPolynomial
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

/-! Literal coprime scalar detector sums, with the two unshared label
normalizers and the original four cofactor coefficients. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] (P : J → Finset ℕ)

def markedPhysicalCoprimeLabelPairs : Finset (ℕ×ℕ) :=
  ((markedMajorLabelSet P).product (markedMajorLabelSet P)).filter (fun z => z.1.Coprime z.2)

def markedPhysicalCoprimeScalarDetectorSum
    (S T : Finset ℕ) (η : ℝ → ℂ) (Y : ℝ)
    (detector : ℤ → ℤ → ℤ → ℂ) (α β : ℕ → ℂ) : ℂ :=
  (markedMajorLabelMass P:ℂ)^2*
    ∑ z ∈ markedPhysicalCoprimeLabelPairs P,
      markedPhysicalScalarDetectorBlock S T η Y detector α β z.1 z.2

def markedPhysicalCoprimeScalarDetectorAbsMass
    (S T : Finset ℕ) (η : ℝ → ℂ) (Y : ℝ)
    (detector : ℤ → ℤ → ℤ → ℂ) (α β : ℕ → ℂ) : ℝ :=
  (markedMajorLabelMass P)^2*
    ∑ z ∈ markedPhysicalCoprimeLabelPairs P,
      markedPhysicalScalarDetectorAbsBlock S T η Y detector α β z.1 z.2

variable [DecidableEq J]
  (hP : ∀ j p,p ∈ P j → p.Prime)
  (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))

include hP hdis

theorem markedPhysicalCoprimeLabelPairs_sum {R : Type*} [AddCommMonoid R] (F : ℕ×ℕ → R) :
    (∑ z ∈ markedPhysicalCoprimeLabelPairs P,F z) =
      ∑ b : (j : J) → ↥(P j),∑ a : (j : J) → ↥(P j),
        if (markedPrimeBandProduct P b).Coprime (markedPrimeBandProduct P a) then
          F (markedPrimeBandProduct P b,markedPrimeBandProduct P a) else 0 := by
  have h (f : ℕ → R) : (∑ n ∈ markedMajorLabelSet P,f n)=
      ∑ t : (j : J) → ↥(P j), f (markedPrimeBandProduct P t) := by
    rw [markedMajorLabelSet,Finset.sum_image (fun _ _ _ _ he =>
      markedPrimeBandProduct_injective P hP hdis he)]
    congr 1
    ext t
    simp
  rw [markedPhysicalCoprimeLabelPairs,Finset.sum_filter]
  refine (Finset.sum_product _ _ _).trans ?_
  simp_rw [h]

end
end ArtinMatthews
