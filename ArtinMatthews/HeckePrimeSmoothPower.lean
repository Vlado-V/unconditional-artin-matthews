module

public import OAI.NumberTheory.DirichletL.Hecke.PrimeAnnular
public import ArtinMatthews.HeckePrimeLongParameters
public import ArtinMatthews.HeckePrimeZeroMaximum
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
public import OAI.NumberTheory.DirichletL.Hecke.PrimeBin


set_option backward.privateInPublic true
@[expose] public section

/-! Actual uniform power cancellation for the smooth ideal-prime polynomial.
The only character restriction is genuine nonprincipality, and the modulus
is bounded by the summation scale. -/

noncomputable section
namespace ArtinMatthews
open OAI.SevenEighths
open scoped ContDiff

theorem heckePrimePolynomial_smooth_power (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ K H₀ : ℝ, 0 < K ∧ 0 < H₀ ∧ ∀ H : ℝ, H₀ ≤ H →
      ∀ η : HeckeFamily.Character, η.residue ≠ 1 → (η.modulus.absNorm : ℝ) ≤ H →
      ∀ t : ℝ, |t| ≤ H^B →
        ‖HeckePrimeAnnular.primePolynomial η W b H 0 t‖ ≤ K*H^(13/32 : ℝ) := by
  obtain ⟨K, hK, hbound⟩ := HeckePrimeAnnular.prime_bin_bound W a b ha hsupp hW
    1 1 (B+1) (1/32) (1/1024) (1/64) (2*(B+1)+4) 0 0
    (by norm_num) (by norm_num) (by linarith) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by linarith) (by norm_num)
  let H₀ := max 5 (Real.exp (2*(|Real.log a|+|Real.log b|)+1))
  refine ⟨K, H₀, hK, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 5) (le_max_left _ _), ?_⟩
  intro H hH η hη hmod t ht
  have hH5 : 5 ≤ H := (le_max_left _ _).trans hH
  have hHp : 0 < H := by linarith
  have hbud := heckePrime_bin_height_budget hH5 hB ht
  have hlog : 2*(|Real.log a|+|Real.log b|)+1 ≤ Real.log H := by
    have h := Real.log_le_log (Real.exp_pos (2*(|Real.log a|+|Real.log b|)+1))
      ((le_max_right _ _).trans hH)
    rwa [Real.log_exp] at h
  have hmax : HeckeDetectorZeros.zeroMaximum (fun _ : Unit => η) (fun _ => hη)
      (3*(0+1 : ℕ)*H^(B+1)) < (7/8 : ℝ)+2*(1/1024) := by
    have h := heckeZeroMaximum_le_seven_eighths (fun _ : Unit => η) (fun _ => hη)
      (3*(0+1 : ℕ)*H^(B+1))
    linarith
  have hh := hbound H 1 (by linarith) (by norm_num) (by norm_num)
    (by simpa only [Real.rpow_one] using (show 2 ≤ H by linarith)) hbud.1
    (fun _ : Unit => η) (fun _ => hη) (7/8) 0 (by norm_num) (by norm_num) hmax
    1 0 t (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simpa only [Real.rpow_one] using hlog) ()
    (by simpa only [Real.rpow_one] using hmod)
    (by simpa only [Nat.mul_zero, Nat.zero_add, Nat.cast_ofNat] using hbud.2.1)
    (by simpa only [Nat.mul_zero, Nat.zero_add, Nat.cast_ofNat, Real.rpow_one] using hbud.2.2)
  convert hh using 1 <;> norm_num

end ArtinMatthews
