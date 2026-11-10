module

public import ArtinMatthews.SourceComparisonTripleMean
public import ArtinMatthews.SourceComparisonHighTimeTuple
public import Mathlib.Analysis.CStarAlgebra.Classes
public import ArtinMatthews.MarkedMajorArcProductMean
public import ArtinMatthews.SourceComparisonSmoothEnergy
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Pass from the sharp product boxes to the literal smooth product cutoff. -/

namespace ArtinMatthews

open Finset Filter MeasureTheory Set
open scoped Topology FourierTransform SchwartzMap ContDiff

noncomputable section

def sourceComparisonCutTriple (S : Finset (ℕ × ℕ × ℕ)) (c : ℕ × ℕ × ℕ → ℂ)
    (ψ : ℝ → ℂ) (Z Y t : ℝ) : ℂ :=
  (∑ v ∈ S, c v*ψ ((sourceComparisonTriplePosition v:ℝ)/Y)*
    markedPrimePhase (sourceComparisonTriplePosition v) t)/Z

theorem sourceComparisonCutTriple_continuous (S : Finset (ℕ × ℕ × ℕ)) (c : ℕ × ℕ × ℕ → ℂ)
    (ψ : ℝ → ℂ) (Z Y : ℝ) : Continuous (sourceComparisonCutTriple S c ψ Z Y) := by
  unfold sourceComparisonCutTriple markedPrimePhase
  fun_prop

/-- A fixed smooth cutoff and a bounded log-power twist preserve any
prescribed high-time saving on a product box. -/
theorem sourceComparisonCutTriple_high_energy
    (ψ : ℝ → ℂ) {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support ψ ⊆ Set.Icc a b) (hψ : ContDiff ℝ ∞ ψ)
    (D C B A : ℝ) (hD : 0 ≤ D) (hA : 0 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (S : Finset (ℕ × ℕ × ℕ)) (c : ℕ × ℕ × ℕ → ℂ) (Z Y T σ : ℝ),
        1 ≤ Z → 0 < Y → X^(max 1 C+1) ≤ T → T ≤ Z → Z ≤ Real.exp (3*X) →
        |σ| ≤ X^C →
        (∀ v ∈ S, sourceComparisonTriplePosition v ∈ Finset.Ioc 0 ⌊8*Z⌋₊) →
        (∀ v ∈ S, ‖c v‖ ≤ X^D) →
        (∫ t in sourceComparisonHighTimes (2*T) (X^B),
          ‖sourceComparisonCutTriple S c (fun _ => 1) Z Y t‖^2) ≤ X^(-A-2) →
        (∫ t in sourceComparisonHighTimes T (X^(max (max 1 C) B+1)),
          ‖sourceComparisonCutTriple S c ψ Z Y (t+σ)‖^2) ≤ X^(-A) := by
  let P := max 1 C
  let Q := max P B
  let K := 576*Real.exp 1*(1+Real.log 8+3)^9
  let j := ⌈2*D+9+A+2⌉₊
  let F : SchwartzMap ℝ ℂ := 𝓕 (primeExtractionLogProfile ψ ha hsupp hψ)
  let M := ∫ ξ : ℝ, ‖F ξ‖
  let Mj := ∫ ξ : ℝ, |ξ|^j*‖F ξ‖
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  let L := 2*M^2+2*Mj^2*K
  filter_upwards [eventually_ge_atTop (max 10 L)] with X hX
  have hX10 : 10 ≤ X := (le_max_left _ _).trans hX
  have hLX : L ≤ X := (le_max_right _ _).trans hX
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  intro S c Z Y T σ hZ hY hT hTZ hcap hσ hS hc hhigh
  let N := ⌊8*Z⌋₊
  let f := markedNaturalPolynomial (Finset.Ioc 0 N) (sourceComparisonTripleCoefficient S c Z)
  let W := sourceComparisonHighTimes T (X^(Q+1))
  have hT0 : 0 < T := (Real.rpow_pos_of_pos hX0 _).trans_le hT
  have huncut (t : ℝ) : f t = sourceComparisonCutTriple S c (fun _ => 1) Z Y t := by
    simpa only [mul_one, sourceComparisonCutTriple, f] using
      sourceComparisonTriplePolynomial_eq S c N hS Z (fun _ => 1) t
  have hmean (ξ : ℝ) :
      (∫ t in W, ‖f (t+σ+2*Real.pi*ξ)‖^2) ≤ K*X^(2*D+9) := by
    have hm := sourceComparisonTriple_translated_mean 3 D X (by norm_num) hX1
      S c Z T (σ+2*Real.pi*ξ) hZ hT0 hTZ hcap hc
    simp only [← add_assoc] at hm
    exact (setIntegral_mono_set (((markedNaturalPolynomial_continuous _ _).comp
      (by fun_prop : Continuous (fun t => t+σ+2*Real.pi*ξ))).norm.pow 2).integrableOn_Icc
      (Eventually.of_forall (fun _ => sq_nonneg _))
      (Eventually.of_forall (fun _ (ht : _ ∈ W) => ht.1))).trans hm
  have hshift (ξ : ℝ) (hξ : ξ ∈ Set.Icc (-X) X) : |σ+2*Real.pi*ξ| ≤ X^(P+1) := by
    have h₁ : X^C ≤ X^P := Real.rpow_le_rpow_of_exponent_le hX1 (le_max_right _ _)
    have h₂ : X ≤ X^P := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hX1 (le_max_left (1:ℝ) C)
    have hpi : 2*Real.pi ≤ 8 := by linarith [Real.pi_lt_four]
    calc
      _ ≤ |σ|+|2*Real.pi*ξ| := abs_add_le _ _
      _ ≤ X^P+8*X^P := by
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2*Real.pi)]
        exact add_le_add (hσ.trans h₁)
          (mul_le_mul hpi ((abs_le.mpr hξ).trans h₂) (abs_nonneg ξ) (by norm_num))
      _ ≤ X*X^P := by nlinarith [Real.rpow_nonneg hX0.le P]
      _ = _ := by rw [Real.rpow_add hX0, Real.rpow_one, mul_comm]
  have hcore (ξ : ℝ) (hξ : ξ ∈ Set.Icc (-X) X) :
      (∫ t in W, ‖f (t+σ+2*Real.pi*ξ)‖^2) ≤ X^(-A-2) := by
    have hs := hshift ξ hξ
    have hTshift : T+|σ+2*Real.pi*ξ| ≤ 2*T := by linarith
    have hSshift : X^B+|σ+2*Real.pi*ξ| ≤ X^(Q+1) := by
      have hB : X^B ≤ X^Q := Real.rpow_le_rpow_of_exponent_le hX1 (le_max_right _ _)
      have hP : X^P ≤ X^Q := Real.rpow_le_rpow_of_exponent_le hX1 (le_max_left _ _)
      have hsharp : |σ+2*Real.pi*ξ| ≤ 9*X^P := by
        have h₁ : X^C ≤ X^P := Real.rpow_le_rpow_of_exponent_le hX1 (le_max_right _ _)
        have h₂ : X ≤ X^P := by
          simpa only [Real.rpow_one] using
            Real.rpow_le_rpow_of_exponent_le hX1 (le_max_left (1:ℝ) C)
        have hpi : 2*Real.pi ≤ 8 := by linarith [Real.pi_lt_four]
        have hh := abs_add_le σ (2*Real.pi*ξ)
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2*Real.pi)] at hh
        have hprod := mul_le_mul hpi ((abs_le.mpr hξ).trans h₂) (abs_nonneg ξ) (by norm_num : 0 ≤ (8:ℝ))
        linarith [hσ.trans h₁]
      rw [Real.rpow_add hX0, Real.rpow_one]
      nlinarith [mul_le_mul_of_nonneg_left hP (by norm_num : 0 ≤ (9:ℝ)),
        Real.rpow_nonneg hX0.le Q]
    have hh := sourceComparisonHighTimes_shift_energy f (markedNaturalPolynomial_continuous _ _)
      T (X^(Q+1)) (2*T) (X^B) (σ+2*Real.pi*ξ) hTshift hSshift
    simp only [← add_assoc] at hh
    exact hh.trans (by simpa only [huncut] using hhigh)
  have hpol := sourceComparison_smoothed_energy ψ ha hsupp hψ (Finset.Ioc 0 N)
    (sourceComparisonTripleCoefficient S c Z) (fun _ hn => (mem_Ioc.mp hn).1)
    Y T (X^(Q+1)) X σ (K*X^(2*D+9)) (X^(-A-2)) hY hX0 j hmean hcore
  have htail : 2*(Mj/X^j)^2*(K*X^(2*D+9)) ≤ 2*Mj^2*K*X^(-A-2) := by
    have hj : 2*D+9+A+2 ≤ (j:ℝ) := Nat.le_ceil _
    have hp : X^(2*D+9)/(X^j)^2 ≤ X^(-A-2) := by
      rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_sub hX0]
      apply Real.rpow_le_rpow_of_exponent_le hX1
      push_cast
      linarith
    calc
      _ = 2*Mj^2*K*(X^(2*D+9)/(X^j)^2) := by rw [div_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)
  have hcut (t : ℝ) : sourceComparisonCutTriple S c ψ Z Y t =
      markedNaturalPolynomial (Finset.Ioc 0 N)
        (fun n => sourceComparisonTripleCoefficient S c Z n*ψ ((n:ℝ)/Y)) t :=
    (sourceComparisonTriplePolynomial_eq S c N hS Z (fun n => ψ ((n:ℝ)/Y)) t).symm
  simp_rw [hcut]
  apply hpol.trans
  calc
    _ ≤ L*X^(-A-2) := by
      change 2*M^2*X^(-A-2)+2*(Mj/X^j)^2*(K*X^(2*D+9)) ≤ _
      exact (add_le_add_right htail _).trans_eq (by dsimp [L]; ring)
    _ ≤ X*X^(-A-2) := mul_le_mul_of_nonneg_right hLX (by positivity)
    _ ≤ _ := by
      conv_lhs => lhs; rw [← Real.rpow_one X]
      rw [← Real.rpow_add hX0]
      apply Real.rpow_le_rpow_of_exponent_le hX1
      linarith

end
end ArtinMatthews
