module

public import ArtinMatthews.IdealFirstCoordinates
public import ArtinMatthews.IdealProbeRemainder
public import ArtinMatthews.IdealRawPairing
public import ArtinMatthews.IdealHarmonicComponents
public import ArtinMatthews.IdealOperatorPairing
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

/-! The two exceptional raw terms use the full-probe energies.
Their sum has no count of subset components. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealLabelNorm_energy_bound {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (hV : ∀ g,0 < bandReciprocalMass (P g))
    (f g : MarkedPhysicalMarking P M → ℂ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hfg : idealLabelEnergy P M f ≤ δ^2*idealLabelEnergy P M g) :
    idealLabelNorm P f ≤ δ*idealLabelNorm P g := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hδ (Real.sqrt_nonneg _))).mp
  change (idealLabelNorm P f)^2 ≤ (δ*idealLabelNorm P g)^2
  rw [mul_pow,idealLabelNorm_sq P hV,idealLabelNorm_sq P hV]
  exact hfg

theorem idealResidual_exception_norm {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (hP : ∀ j p,p∈P j → 0 < p) (S T : Finset (G × Fin k)) (Θ ζ : ℝ)
    (f g : MarkedPhysicalMarking P (k+ell) → ℂ) :
    ‖idealRawPairing P Θ ζ
      (idealProbeProjection P (idealFirstCoordinates ell S)
        (idealPatternFreeCoordinates (fun _ : G => (∅ : Finset (Fin k)))) f)
      (idealAverageSet P (idealPatternFreeCoordinates (fun _ : G => (∅ : Finset (Fin k)))) g)+
    idealRawPairing P Θ ζ
      (idealProbeRemainder P (idealFirstCoordinates ell S)
        (idealPatternFreeCoordinates (fun _ : G => (∅ : Finset (Fin k)))) f)
      (idealProbeProjection P (idealFirstCoordinates ell T)
        (idealPatternFreeCoordinates (fun _ : G => (∅ : Finset (Fin k)))) g)‖ ≤
    idealLabelNorm P (idealProbeProjection P (idealFirstCoordinates ell S)
      (idealPatternFreeCoordinates (fun _ : G => (∅ : Finset (Fin k)))) f)*idealLabelNorm P g+
    idealLabelNorm P f*idealLabelNorm P (idealProbeProjection P (idealFirstCoordinates ell T)
      (idealPatternFreeCoordinates (fun _ : G => (∅ : Finset (Fin k)))) g) := by
  have htail : idealLabelNorm P (idealAverageSet P
      (idealPatternFreeCoordinates (fun _ : G => (∅ : Finset (Fin k)))) g) ≤ idealLabelNorm P g :=
    Real.sqrt_le_sqrt (idealAverageSet_energy_le P hV _ g)
  have hrem : idealLabelNorm P (idealProbeRemainder P (idealFirstCoordinates ell S)
      (idealPatternFreeCoordinates (fun _ : G => (∅ : Finset (Fin k)))) f) ≤ idealLabelNorm P f :=
    Real.sqrt_le_sqrt (idealProbeRemainder_energy_le_harmonic P hV hP _ _ f)
  exact (norm_add_le _ _).trans (add_le_add
    ((idealRawPairing_norm_le P hV hP Θ ζ _ _).trans
      (mul_le_mul_of_nonneg_left htail (Real.sqrt_nonneg _)))
    ((idealRawPairing_norm_le P hV hP Θ ζ _ _).trans
      (mul_le_mul_of_nonneg_right hrem (Real.sqrt_nonneg _))))

end
end ArtinMatthews
