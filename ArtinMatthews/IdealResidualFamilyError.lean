module

public import ArtinMatthews.IdealResidualFamilyPairing
public import ArtinMatthews.IdealFirstCoordinates
public import ArtinMatthews.IdealProbeRemainder
public import ArtinMatthews.IdealSelectedComparisonTransport
public import ArtinMatthews.IdealRawAlgebra
public import ArtinMatthews.IdealResidualErrorCount
public import ArtinMatthews.IdealResidualPatternError
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The entire original residual family is its two full-probe terms
plus the sum of the actual comparison errors. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def idealResidualExceptionalPairing {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (S T : Finset (G × Fin k)) (Θ ζ : ℝ)
    (f g : MarkedPhysicalMarking P (k+ell) → ℂ) : ℂ :=
  idealRawPairing P Θ ζ
    (idealProbeProjection P (idealFirstCoordinates ell S)
      (idealPatternFreeCoordinates (fun _ : G => (∅ : Finset (Fin k)))) f)
    (idealAverageSet P (idealPatternFreeCoordinates (fun _ : G => (∅ : Finset (Fin k)))) g)+
  idealRawPairing P Θ ζ
    (idealProbeRemainder P (idealFirstCoordinates ell S)
      (idealPatternFreeCoordinates (fun _ : G => (∅ : Finset (Fin k)))) f)
    (idealProbeProjection P (idealFirstCoordinates ell T)
      (idealPatternFreeCoordinates (fun _ : G => (∅ : Finset (Fin k)))) g)

theorem idealResidualFamily_error_identity {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (S T : Finset (G × Fin k)) (Q : ℕ) (h ξ Θ ζ : ℝ)
    (f g : MarkedPhysicalMarking P (k+ell) → ℂ) (hf : IdealSymmetric f) (hg : IdealSymmetric g) :
    idealLabelPairing P f (idealResidualOperator P S T Q h ξ Θ ζ g)=
    idealResidualExceptionalPairing P S T Θ ζ f g+
      ∑ A∈S.powerset.erase ∅,∑ B∈T.powerset.erase ∅,
        (idealResidualPatternPairing P (some (A,B)) Q h ξ Θ ζ f g+
          (-1:ℂ)^(A.card+B.card)*idealRawPairing P Θ ζ
            (idealAverageSet P (idealPatternFreeCoordinates (idealResidualFreeSlots A)) f)
            (idealAverageSet P (idealPatternFreeCoordinates (idealResidualFreeSlots B)) g)) := by
  have hc := idealResidual_raw_cancellation P S T Θ ζ f g
  change _ = idealResidualExceptionalPairing P S T Θ ζ f g at hc
  rw [idealResidualOperator_pairing_expansion P hV S T Q h ξ Θ ζ f g hf hg,← hc]
  simp only [sum_add_distrib]
  ring

theorem idealResidualFamily_pairing_bound {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (hP : ∀ j p,p∈P j → 0 < p) (S T : Finset (G × Fin k)) (hST : Disjoint S T)
    (Q : ℕ) (h ξ Θ ζ : ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hcmp : ∀ A∈S.powerset.erase ∅,∀ B∈T.powerset.erase ∅,∀ α u v,
      ‖idealSelectedComparisonForm (idealResidualBands P A) (idealResidualBands P B) Q h ξ ζ α u v‖ ≤
      ε*Real.sqrt (idealFrameEnergy (idealSelectedMass (idealResidualBands P A)) u)*
        Real.sqrt (idealFrameEnergy (idealSelectedMass (idealResidualBands P B)) v))
    (f g : MarkedPhysicalMarking P (k+ell) → ℂ) (hf : IdealSymmetric f) (hg : IdealSymmetric g) :
    ‖idealLabelPairing P f (idealResidualOperator P S T Q h ξ Θ ζ g)‖ ≤
      ‖idealResidualExceptionalPairing P S T Θ ζ f g‖+
        (2:ℝ)^(S.card+T.card)*ε*idealLabelNorm P f*idealLabelNorm P g := by
  let E := fun A B : Finset (G × Fin k) =>
    idealResidualPatternPairing P (some (A,B)) Q h ξ Θ ζ f g+
      (-1:ℂ)^(A.card+B.card)*idealRawPairing P Θ ζ
        (idealAverageSet P (idealPatternFreeCoordinates (idealResidualFreeSlots A)) f)
        (idealAverageSet P (idealPatternFreeCoordinates (idealResidualFreeSlots B)) g)
  have hE (A : Finset (G × Fin k)) (hA : A∈S.powerset.erase ∅)
      (B : Finset (G × Fin k)) (hB : B∈T.powerset.erase ∅) :
      ‖E A B‖ ≤ ε*idealLabelNorm P f*idealLabelNorm P g := by
    have hAB : Disjoint A B := hST.mono (mem_powerset.mp (mem_of_mem_erase hA))
      (mem_powerset.mp (mem_of_mem_erase hB))
    exact idealResidualPattern_error_bound P hV hP A B hAB Q h ξ Θ ζ hε (hcmp A hA B hB) f g
  have herr := idealResidualErrors_norm S T E
    (mul_nonneg (mul_nonneg hε (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)) hE
  have herr' : ‖∑ A∈S.powerset.erase ∅,∑ B∈T.powerset.erase ∅,E A B‖ ≤
      (2:ℝ)^(S.card+T.card)*ε*idealLabelNorm P f*idealLabelNorm P g := by
    simpa only [mul_assoc,idealLabelNorm] using herr
  rw [idealResidualFamily_error_identity P hV S T Q h ξ Θ ζ f g hf hg]
  exact (norm_add_le _ _).trans (add_le_add le_rfl herr')

end
end ArtinMatthews
