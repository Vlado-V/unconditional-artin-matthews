module

public import ArtinMatthews.IdealRawPattern
public import ArtinMatthews.IdealLabelPairing
public import ArtinMatthews.IdealAveragePairing
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
public import Mathlib.RingTheory.PiTensorProduct
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

/-! The raw pairing retains its full product phase. Its two tail
averages and its unit bilinear bound are exact. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def idealRawPairing {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (Θ ζ : ℝ)
    (f g : MarkedPhysicalMarking P (k+ell) → ℂ) : ℂ :=
  idealLabelPairing P f (fun a => idealRawPhase Θ ζ a*g a)

theorem idealRawPairing_norm_le {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (hV : ∀ g,0 < bandReciprocalMass (P g))
    (hP : ∀ g p,p∈P g → 0 < p) (Θ ζ : ℝ)
    (f g : MarkedPhysicalMarking P (k+ell) → ℂ) :
    ‖idealRawPairing P Θ ζ f g‖ ≤ idealLabelNorm P f*idealLabelNorm P g := by
  have h := idealLabelPairing_phase_norm_le P hV f g (idealRawPhase Θ ζ) (idealRawPhase_norm hP Θ ζ)
  simpa only [idealRawPairing,mul_comm] using h

theorem idealPattern_raw_pairing {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (hV : ∀ g,0 < bandReciprocalMass (P g))
    (Θ ζ : ℝ) (f g : MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealLabelPairing P f (idealPatternApplyWithLaws (fun j => markedHarmonicAtom (P j))
      (fun j => markedHarmonicAtom (P j)) (fun _ => (∅ : Finset (Fin k))) Θ ζ (fun _ _ _ => 1) g)=
      idealRawPairing P Θ ζ
        (idealAverageSet P (idealPatternFreeCoordinates (fun _ => (∅ : Finset (Fin k)))) f)
        (idealAverageSet P (idealPatternFreeCoordinates (fun _ => (∅ : Finset (Fin k)))) g) := by
  let S := idealPatternFreeCoordinates (ell:=ell) (fun _ : G => (∅ : Finset (Fin k)))
  let H := fun a => idealRawPhase Θ ζ a*idealAverageSet P S g a
  have hH : idealAverageSet P S H=H := by
    rw [idealAverageSet_mul_of_independent P S (idealRawPhase Θ ζ)
      (idealAverageSet P S g) (idealRawPhase_tail_independent Θ ζ)]
    rw [idealAverageSet_idempotent P hV]
  calc
    _ = idealLabelPairing P f H := by
      congr 1
      funext a
      exact idealPatternApply_raw P hV Θ ζ g a
    _ = idealLabelPairing P (idealAverageSet P S f) H := by
      rw [idealLabelPairing_average_adjoint P S,hH]
    _ = _ := rfl

theorem idealRawPairing_add_left {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (Θ ζ : ℝ)
    (f₁ f₂ g : MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealRawPairing P Θ ζ (fun a => f₁ a+f₂ a) g=
      idealRawPairing P Θ ζ f₁ g+idealRawPairing P Θ ζ f₂ g := by
  unfold idealRawPairing idealLabelPairing
  simp only [star_add,mul_add,add_mul,sum_add_distrib]

theorem idealRawPairing_add_right {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (Θ ζ : ℝ)
    (f g₁ g₂ : MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealRawPairing P Θ ζ f (fun a => g₁ a+g₂ a)=
      idealRawPairing P Θ ζ f g₁+idealRawPairing P Θ ζ f g₂ := by
  unfold idealRawPairing idealLabelPairing
  simp only [mul_add,sum_add_distrib]

end
end ArtinMatthews
