module

public import ArtinMatthews.CubicReciprocityNonprincipalCharacterBase
public import ArtinMatthews.PrimeExtractionSeparatedCoefficients
public import ArtinMatthews.HeckeCubicPrimeIntervals
public import ArtinMatthews.PrimeExtractionPrimeTestIdentity
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

/-! The genuine long-frequency character tests for the literal extracted
prime coefficient. The rough cutoff and retained Mellin frequency remain
explicit and uniform. -/

noncomputable section
namespace ArtinMatthews
open OAI.SevenEighths Filter
open scoped BigOperators Classical

theorem primeExtractionFirstPhaseCoefficient_all_log (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y^3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r)
    (A₀ B δ D R : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) (hD : 0 < D) :
    ∀ᶠ x : ℝ in atTop, ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log x)^A₀ →
      ∀ (ϑ : DirichletCharacter ℂ q) (H : ℝ), x^δ ≤ H →
      ∀ m n : ℕ, m ≤ n → H ≤ m → (n : ℝ) ≤ 2*H →
      ∀ z : ℝ, 0 ≤ z → ∀ v t : ℝ, |v| ≤ (Real.log x)^R → |t| ≤ x^B →
      ‖markedTwistedSum (Finset.Icc m n)
        (primeExtractionFirstPhaseCoefficient (cubicNumeratorHeckeCharacter A hA) χ z v)
        ϑ t‖ ≤ 35*H*(Real.log x)^(-D) := by
  filter_upwards [cubicNumeratorPrimeInterval_fixed_twist_all_log A hA hnoncube χ
      A₀ (B+2) δ D (by linarith) hδ hD,
    primeExtraction_retained_frequency_bound B R hB,
    eventually_gt_atTop (1 : ℝ)] with x hprime hfreq hx
  intro q _ hq ϑ H hH m n _ hmH hnH z hz v t hv ht
  rw [primeExtractionFirstPhaseCoefficient_interval_test _ χ ϑ hz v t m n]
  by_cases hmn : max m (⌊z⌋₊+1) ≤ n
  · exact hprime q hq ϑ H hH _ n hmn
      (hmH.trans (by exact_mod_cast le_max_left m (⌊z⌋₊+1))) hnH
      _ (hfreq t v ht hv)
  · have hempty : Finset.Icc (max m (⌊z⌋₊+1)) n = ∅ := Finset.Icc_eq_empty hmn
    rw [hempty]
    simp only [Finset.filter_empty, Finset.sum_empty, norm_zero]
    have hHpos : 0 < H := (Real.rpow_pos_of_pos (by linarith : 0 < x) δ).trans_le hH
    exact mul_nonneg (mul_nonneg (by norm_num) hHpos.le)
      (Real.rpow_nonneg (Real.log_pos hx).le _)

theorem primeExtractionFirstPhaseCoefficient_normalized_all_log (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y^3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r)
    (A₀ B δ D R : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) (hD : 0 < D) :
    ∀ᶠ x : ℝ in atTop, ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log x)^A₀ →
      ∀ (ϑ : DirichletCharacter ℂ q) (H : ℝ), x^δ ≤ H →
      ∀ m n : ℕ, m ≤ n → H ≤ m → (n : ℝ) ≤ 2*H →
      ∀ z : ℝ, 0 ≤ z → ∀ v t : ℝ, |v| ≤ (Real.log x)^R → |t| ≤ x^B →
      ‖markedTwistedSum (Finset.Icc m n)
        (primeExtractionFirstPhaseCoefficient (cubicNumeratorHeckeCharacter A hA) χ z v)
        ϑ t‖ / H ≤ 35*(Real.log x)^(-D) := by
  filter_upwards [primeExtractionFirstPhaseCoefficient_all_log A hA hnoncube χ
    A₀ B δ D R hB hδ hD, eventually_gt_atTop (0 : ℝ)] with x hprime hx
  intro q _ hq ϑ H hH m n hmn hmH hnH z hz v t hv ht
  have hHpos : 0 < H := (Real.rpow_pos_of_pos hx δ).trans_le hH
  apply (div_le_iff₀ hHpos).mpr
  exact (hprime q hq ϑ H hH m n hmn hmH hnH z hz v t hv ht).trans_eq (by ring)

end ArtinMatthews
