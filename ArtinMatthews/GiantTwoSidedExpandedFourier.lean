module

public import ArtinMatthews.GiantTwoSidedIndependentFourier
public import ArtinMatthews.GiantTwoSidedPhysicalFourier
public import ArtinMatthews.GiantTwoSidedExpandedRootTransfer
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
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Return-Fourier inversion commutes with every original finite
pattern, permutation and auxiliary sum and its slot normalization. -/
namespace ArtinMatthews
open MeasureTheory Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {I J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ}
  [∀ p : ↥(markedPhysicalBandPrimes P), NeZero p.val] {k ell n : ℕ}

def giantTwoSidedExpandedIndependentUnrestrictedMoment (patterns : Fin n → Finset I)
    (C : Fin n → I → J → Finset (Fin k)) (step : Fin n → ℤ) (q : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i ν, GiantTwoSidedPatternCoefficient P (C i ν) ell) : ℂ :=
  ((giantTwoSidedResidueSlotNormalization (J := J) (k + ell)) ^ n : ℂ) *
    ∑ choices : (i : Fin n) → GiantTwoSidedResidueEdgeChoice (P := P) (patterns i) (C i) ell,
      giantTwoSidedIndependentUnrestrictedMoment (fun i => C i (choices i).1.val)
        (fun i => (choices i).2.1) (fun i => (choices i).2.2.1)
        (fun i => (choices i).2.2.2) step q ζ (fun i => K i (choices i).1.val)

def giantTwoSidedExpandedIndependentFourierMoment (patterns : Fin n → Finset I)
    (C : Fin n → I → J → Finset (Fin k)) (step : Fin n → ℤ) (q : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i ν, GiantTwoSidedPatternCoefficient P (C i ν) ell)
    (θ : AddCircle (1 : ℝ)) : ℂ :=
  ((giantTwoSidedResidueSlotNormalization (J := J) (k + ell)) ^ n : ℂ) *
    ∑ choices : (i : Fin n) → GiantTwoSidedResidueEdgeChoice (P := P) (patterns i) (C i) ell,
      giantTwoSidedIndependentFourierMoment (fun i => C i (choices i).1.val)
        (fun i => (choices i).2.1) (fun i => (choices i).2.2.1)
        (fun i => (choices i).2.2.2) step q ζ (fun i => K i (choices i).1.val) θ

theorem giantTwoSidedExpandedIndependentFourier_continuous (patterns : Fin n → Finset I)
    (C : Fin n → I → J → Finset (Fin k)) (step : Fin n → ℤ) (q : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i ν, GiantTwoSidedPatternCoefficient P (C i ν) ell) :
    Continuous (giantTwoSidedExpandedIndependentFourierMoment patterns C step q ζ K) := by
  unfold giantTwoSidedExpandedIndependentFourierMoment
  apply continuous_const.mul
  apply continuous_finsetSum
  intro choices _
  exact giantTwoSidedIndependentFourier_continuous _ _ _ _ _ _ _ _

theorem giantTwoSidedExpandedIndependentMoment_fourier (patterns : Fin n → Finset I)
    (C : Fin n → I → J → Finset (Fin k)) (step : Fin n → ℤ) (q : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i ν, GiantTwoSidedPatternCoefficient P (C i ν) ell) :
    giantTwoSidedExpandedIndependentMoment patterns C step q ζ K =
      ∫ θ : AddCircle (1 : ℝ),
        giantTwoSidedExpandedIndependentFourierMoment patterns C step q ζ K θ
          ∂AddCircle.haarAddCircle := by
  symm
  unfold giantTwoSidedExpandedIndependentFourierMoment giantTwoSidedExpandedIndependentMoment
  rw [integral_const_mul, integral_finsetSum]
  · congr 1
    apply sum_congr rfl
    intro choices _
    exact (giantTwoSidedIndependentMoment_fourier _ _ _ _ _ _ _ _).symm
  · intro choices _
    exact giantTwoSidedIndependentFourier_integrable _ _ _ _ _ _ _ _

theorem giantTwoSidedExpandedIndependentMoment_unitInterval (patterns : Fin n → Finset I)
    (C : Fin n → I → J → Finset (Fin k)) (step : Fin n → ℤ) (q : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i ν, GiantTwoSidedPatternCoefficient P (C i ν) ell) :
    giantTwoSidedExpandedIndependentMoment patterns C step q ζ K =
      ∫ θ in (0 : ℝ)..1,
        giantTwoSidedExpandedIndependentFourierMoment patterns C step q ζ K
          (θ : AddCircle (1 : ℝ)) := by
  rw [giantTwoSidedExpandedIndependentMoment_fourier]
  have h := fourierCoeff_eq_intervalIntegral
    (giantTwoSidedExpandedIndependentFourierMoment patterns C step q ζ K) 0 0
  simpa only [fourierCoeff, neg_zero, fourier_zero, one_smul, div_one, zero_add] using h

theorem giantTwoSidedExpandedIndependentFourier_twisted (patterns : Fin n → Finset I)
    (C : Fin n → I → J → Finset (Fin k)) (step : Fin n → ℤ) (q : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i ν, GiantTwoSidedPatternCoefficient P (C i ν) ell)
    (θ : AddCircle (1 : ℝ)) :
    giantTwoSidedExpandedIndependentFourierMoment patterns C step q ζ K θ =
      giantTwoSidedExpandedIndependentUnrestrictedMoment patterns C step q ζ
        (fun i ν => giantTwoSidedFourierCoefficient θ (step i) (K i ν)) := by
  simp only [giantTwoSidedExpandedIndependentFourierMoment,
    giantTwoSidedExpandedIndependentUnrestrictedMoment, giantTwoSidedIndependentFourier_twisted]

theorem giantTwoSidedExpandedIndependentMoment_norm_le (patterns : Fin n → Finset I)
    (C : Fin n → I → J → Finset (Fin k)) (step : Fin n → ℤ) (q : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i ν, GiantTwoSidedPatternCoefficient P (C i ν) ell) {B : ℝ}
    (hB : ∀ θ : AddCircle (1 : ℝ),
      ‖giantTwoSidedExpandedIndependentUnrestrictedMoment patterns C step q ζ
        (fun i ν => giantTwoSidedFourierCoefficient θ (step i) (K i ν))‖ ≤ B) :
    ‖giantTwoSidedExpandedIndependentMoment patterns C step q ζ K‖ ≤ B := by
  rw [giantTwoSidedExpandedIndependentMoment_fourier]
  have h := norm_integral_le_of_norm_le_const
    (μ := AddCircle.haarAddCircle) (Filter.Eventually.of_forall fun θ =>
      (giantTwoSidedExpandedIndependentFourier_twisted patterns C step q ζ K θ).symm ▸ hB θ)
  simpa only [probReal_univ, mul_one] using h

def giantTwoSidedExpandedPhysicalUnrestrictedMoment (patterns : Fin n → Finset I)
    (C : Fin n → I → J → Finset (Fin k)) (step : Fin n → ℤ) (q : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i ν, GiantTwoSidedPatternCoefficient P (C i ν) ell) (roots slice : Finset ℕ) : ℂ :=
  ((giantTwoSidedResidueSlotNormalization (J := J) (k + ell)) ^ n : ℂ) *
    ∑ choices : (i : Fin n) → GiantTwoSidedResidueEdgeChoice (P := P) (patterns i) (C i) ell,
      giantTwoSidedPhysicalUnrestrictedMoment (fun i => C i (choices i).1.val)
        (fun i => (choices i).2.1) (fun i => (choices i).2.2.1)
        (fun i => (choices i).2.2.2) step q ζ (fun i => K i (choices i).1.val) roots slice

omit [∀ p : ↥(markedPhysicalBandPrimes P), NeZero p.val] in
theorem giantTwoSidedExpandedPhysicalMoment_fourier (patterns : Fin n → Finset I)
    (C : Fin n → I → J → Finset (Fin k)) (step : Fin n → ℤ) (q : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i ν, GiantTwoSidedPatternCoefficient P (C i ν) ell) (roots slice : Finset ℕ) :
    giantTwoSidedExpandedPhysicalMoment patterns C step q ζ K roots slice =
      ∫ θ : AddCircle (1 : ℝ),
        giantTwoSidedExpandedPhysicalUnrestrictedMoment patterns C step q ζ
          (fun i ν => giantTwoSidedFourierCoefficient θ (step i) (K i ν)) roots slice
            ∂AddCircle.haarAddCircle := by
  symm
  unfold giantTwoSidedExpandedPhysicalUnrestrictedMoment giantTwoSidedExpandedPhysicalMoment
  rw [integral_const_mul, integral_finsetSum]
  · congr 1
    apply sum_congr rfl
    intro choices _
    exact (giantTwoSidedPhysicalMoment_fourier _ _ _ _ _ _ _ _ roots slice).symm
  · intro choices _
    exact (giantTwoSidedPhysicalFourier_continuous _ _ _ _ _ _ _ _ roots slice).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

end
end ArtinMatthews
