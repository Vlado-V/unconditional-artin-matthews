module

public import ArtinMatthews.MarkedPhysicalBadArcFamily
public import ArtinMatthews.MarkedPhysicalRootHaarMain
public import ArtinMatthews.FixedURootMassShift
public import ArtinMatthews.MarkedPhysicalRootHaarBound
public import ArtinMatthews.MarkedRawBadRootArcIntegral
public import ArtinMatthews.MarkedRootArcFamilies
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

/-! The actual first/second-bad root main term is logarithmically small.
All arc coefficients are the literal fresh harmonic masses divided by
the actual beta threshold.  The special-linear density stays explicit. -/

noncomputable section
namespace ArtinMatthews
open Filter MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysicalBadRootPositiveMain_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10 : ℝ) ≤ e j) (hinj : Function.Injective e) (T : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ d₀ Y : ℝ,
      Real.exp ((Real.log x)^(1/10 : ℝ)) ≤ Y →
      ∀ (source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
        (S : ℕ), Squarefree S →
        ∀ A B C D : ℝ, A ≤ B → C ≤ D →
        ∀ (d b a : ℤ) (R Q W : ℝ) (ψ : ℝ → ℂ),
          1 ≤ Q → 1 ≤ Y → 0 ≤ R → 0 ≤ W →
          (∀ u, ‖ψ u‖ ≤ W) → (∀ u, ψ u ≠ 0 → |u| ≤ R) →
          markedPhysicalRootPositiveMain Finset.univ S A B C D
            (markedPhysicalBadArcLower e x source d₀ Y)
            (markedPhysicalBadArcUpper e x source d₀ Y)
            (markedPhysicalBadArcCoefficient e x source d₀ Y) d b a R Y Q ψ ≤
          ((B-A)*(D-C)/((riemannZeta 2).re*
            (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))) *
            ((33*W*(8*R+5))*Q^3) * (Real.log x)^(-T) := by
  have hμ := eventually_all.mpr (fun I : Finset J =>
    marked_actual_harmonic_fresh_probability_eventually (fun j : ↥(Finset.univ \ I) => e j.1)
      (fun j => by linarith [he j.1]))
  filter_upwards [hμ, markedRootArc_actual_widths_eventually e he,
    markedRawBadRootArc_integral_log_saving e he hinj T] with x hμx hwidth hmass
  intro d₀ Y hY source S hS A B C D hAB hCD d b a R Q W ψ hQ hYone hR hW hψ hsupp
  have hi : (∫ r : ℝ, markedPhysicalIntervalMajorant Finset.univ
      (markedPhysicalBadArcLower e x source d₀ Y)
      (markedPhysicalBadArcUpper e x source d₀ Y)
      (markedPhysicalBadArcCoefficient e x source d₀ Y) r) =
      ∫ θ : AddCircle (1 : ℝ), markedRawBadRootArcMajorant e x d₀ Y source θ := by
    apply markedPhysicalIntervalMajorant_integral_eq_haar
    · exact fun i _ => (markedPhysicalBadArc_bounds e x source d₀ Y i).1
    · exact fun i _ => (markedPhysicalBadArc_bounds e x source d₀ Y i).2
    · intro r hr
      exact markedPhysicalBadArcFamily_eq e x source d₀ Y hr.1 hr.2 (hwidth.2 Y hY).2
        (fun j => (hwidth.1 j).2)
  have hm := markedPhysicalRootPositiveMain_le Finset.univ hS A B C D hAB hCD
    (markedPhysicalBadArcLower e x source d₀ Y)
    (markedPhysicalBadArcUpper e x source d₀ Y)
    (markedPhysicalBadArcCoefficient e x source d₀ Y)
    (fun i _ => markedPhysicalBadArcCoefficient_nonneg e x source d₀ Y
      (fun I => (hμx I).1) i) d b a ψ hQ hYone hR hW hψ hsupp
  rw [hi] at hm
  apply hm.trans
  apply mul_le_mul_of_nonneg_left (hmass d₀ Y hY source)
  have hd : 0 ≤ (B-A)*(D-C)/((riemannZeta 2).re*
      (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ)) := by
    rw [div_eq_mul_inv]
    exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hAB) (sub_nonneg.mpr hCD))
      (by simpa only [one_div] using (fixedURoot_normalized_density_bounds hS).1)
  exact mul_nonneg hd (by positivity)

end ArtinMatthews
