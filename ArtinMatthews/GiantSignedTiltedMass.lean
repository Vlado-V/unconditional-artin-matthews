module

public import ArtinMatthews.GiantSignedTiltedLaw
public import ArtinMatthews.GiantSignedTiltBandBounds
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The actual tilted prime law has its derived total mass. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedTiltedPrimeLaw_sum_bounds (P : Finset ℕ) {n : ℕ} (q : Fin n → ℝ)
    (hV : 0 < bandReciprocalMass P) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (Pmin : ℝ) (hPmin : 0 < Pmin) (hp : ∀ p : P, Pmin ≤ p.val)
    (hsmall : (n : ℝ) / Pmin < 1) :
    1 ≤ ∑ p : P, giantSignedTiltedPrimeLaw P q p ∧
      (∑ p : P, giantSignedTiltedPrimeLaw P q p) ≤ (1 - (n : ℝ) / Pmin)⁻¹ := by
  classical
  constructor
  · calc
      1 = ∑ p : P, markedHarmonicAtom P p := (markedHarmonicAtom_sum P hV).symm
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p _
        rw [giantSignedTiltedPrimeLaw_eq]
        have h := (giantSignedPrimeDensity_band_bounds q hq0 hq1 Pmin hPmin (hp p) hsmall).1
        nlinarith [markedHarmonicAtom_nonneg P hV (p := p)]
  · calc
      _ ≤ ∑ p : P, markedHarmonicAtom P p * (1 - (n : ℝ) / Pmin)⁻¹ := by
        apply Finset.sum_le_sum
        intro p _
        rw [giantSignedTiltedPrimeLaw_eq]
        exact mul_le_mul_of_nonneg_left
          (giantSignedPrimeDensity_band_bounds q hq0 hq1 Pmin hPmin (hp p) hsmall).2
          (markedHarmonicAtom_nonneg P hV)
      _ = _ := by rw [← Finset.sum_mul, markedHarmonicAtom_sum P hV, one_mul]

theorem giantSignedTiltedPrimeLaw_sum_le_two (P : Finset ℕ) {n : ℕ} (q : Fin n → ℝ)
    (hV : 0 < bandReciprocalMass P) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (Pmin : ℝ) (hPmin : 0 < Pmin) (hp : ∀ p : P, Pmin ≤ p.val)
    (hsmall : (n : ℝ) / Pmin ≤ 1 / 2) :
    (∑ p : P, giantSignedTiltedPrimeLaw P q p) ≤ 2 := by
  have hlt : (n : ℝ) / Pmin < 1 := by linarith
  apply (giantSignedTiltedPrimeLaw_sum_bounds P q hV hq0 hq1 Pmin hPmin hp hlt).2.trans
  have hb : 0 < 1 - (n : ℝ) / Pmin := by linarith
  rw [← one_div]
  apply (div_le_iff₀ hb).mpr
  linarith

end
end ArtinMatthews
