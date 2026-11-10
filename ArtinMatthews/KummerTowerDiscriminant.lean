module

public import ArtinMatthews.KummerCyclotomicTowerBase
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import ArtinMatthews.KummerCyclotomicTower
public import ArtinMatthews.KummerSplittingDiscriminantBound
public import ArtinMatthews.KummerTowerDiscriminantBasis
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Polynomial logarithmic discriminant control for the actual auxiliary
cyclotomic/Kummer compositum. -/
noncomputable section
namespace ArtinMatthews

private theorem factorial_mul_pow_sq_le_rank {d Q : ℕ} (_hQ : 1 ≤ Q) (hd : d ≤ Q ^ 2) :
    ((d.factorial : ℝ) * (Q : ℝ) ^ d) ^ 2 ≤ (Q : ℝ) ^ (6 * d) := by
  have hdR : (d : ℝ) ≤ (Q : ℝ)^2 := by exact_mod_cast hd
  have hf : (d.factorial : ℝ) ≤ (d : ℝ)^d := by exact_mod_cast Nat.factorial_le_pow d
  have hpow : (d : ℝ)^d ≤ ((Q : ℝ)^2)^d := pow_le_pow_left₀ (by positivity) hdR d
  calc
    _ ≤ (((Q : ℝ)^2)^d * (Q : ℝ)^d)^2 := by
      gcongr
      exact hf.trans hpow
    _ = (Q : ℝ)^(6*d) := by
      rw [← pow_mul, ← pow_add, ← pow_mul]
      congr 1
      omega

/-- The exact auxiliary field has log-discriminant O(q² log q). -/
theorem twelfthKummerField_abs_discr_le (q : ℕ) (a : ℤ) [NeZero q] [NeZero a]
    (haq : a.natAbs ≤ q) :
    |(NumberField.discr (twelfthKummerField q a) : ℝ)| ≤ (12 * q : ℝ) ^ (72 * q ^ 2) := by
  obtain ⟨b, hb, hheight⟩ := twelfthKummerField_integral_bounded_basis q a haq
  have hheight' (σ : twelfthKummerField q a →ₐ[ℚ] ℂ) i :
      ‖σ (b i)‖ ≤ (12 * q : ℕ) := by
    apply (hheight σ i).trans
    exact_mod_cast (show q ≤ 12 * q by omega)
  have hbound := KummerDiscriminant.abs_discr_le_integral_basis_height b hb
    (Nat.cast_nonneg (12 * q)) hheight'
  have hd := twelfthKummerField_absolute_finrank_le q a
  have hd' : Module.finrank ℚ (twelfthKummerField q a) ≤ (12 * q)^2 := by nlinarith
  have hnum := factorial_mul_pow_sq_le_rank (show 1 ≤ 12 * q by have := NeZero.pos q; omega) hd'
  have hbound' : |(NumberField.discr (twelfthKummerField q a) : ℝ)| ≤
      ((12 * q : ℕ) : ℝ) ^ (6 * Module.finrank ℚ (twelfthKummerField q a)) :=
    by
      apply le_trans _ hnum
      simpa only [Fintype.card_fin] using hbound
  have hexp : 6 * Module.finrank ℚ (twelfthKummerField q a) ≤ 72 * q ^ 2 := by omega
  have hbase : (1 : ℝ) ≤ ((12 * q : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ 12 * q by have := NeZero.pos q; omega)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    hbound'.trans (pow_le_pow_right₀ hbase hexp)

theorem twelfthKummerField_log_discr_le (q : ℕ) (a : ℤ) [NeZero q] [NeZero a]
    (haq : a.natAbs ≤ q) :
    Real.log |(NumberField.discr (twelfthKummerField q a) : ℝ)| ≤
      72 * (q : ℝ)^2 * Real.log (12 * q) := by
  have hD : 0 < |(NumberField.discr (twelfthKummerField q a) : ℝ)| :=
    abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero (twelfthKummerField q a))
  have hQ : 0 < (12 * q : ℝ) := by have := NeZero.pos q; positivity
  have h := (Real.log_le_log_iff hD (pow_pos hQ _)).mpr (twelfthKummerField_abs_discr_le q a haq)
  rw [Real.log_pow] at h
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h

/-- The actual second relative degree is at most the auxiliary cyclotomic degree. -/
theorem twelfthKummerField_finrank_over_kummer_le (q : ℕ) (a : ℤ) [NeZero q] [NeZero a] :
    Module.finrank (primeKummerField q a) (twelfthKummerField q a) ≤ 12 * q := by
  have ht : 0 < Nat.totient (12 * q) := Nat.totient_pos.mpr (by have := NeZero.pos q; omega)
  exact (Nat.le_of_dvd ht (twelfthKummerField_finrank_over_kummer_dvd_totient q a)).trans
    (Nat.totient_le _)

end ArtinMatthews
