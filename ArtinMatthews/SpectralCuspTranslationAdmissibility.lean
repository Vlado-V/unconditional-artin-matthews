module

public import ArtinMatthews.AtkinLehnerMixedPhase
public import ArtinMatthews.KloostermanDoubleCoset
public import ArtinMatthews.SpectralCuspFourierODEHorizontal
public import ArtinMatthews.SpectralCuspTwoCellFourier
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual integral cusp translations and their frequency condition.  A
smaller cusp period is usable only together with its divisibility condition. -/

noncomputable section
open Matrix
open scoped MatrixGroups

namespace ArtinMatthews

set_option backward.isDefEq.respectTransparency false in
theorem cusp_conjugate_translation_lower (r : SL(2, ℤ)) (k : ℤ) :
    (r⁻¹ * integerTranslation k * r) 1 0 = -k * (r 1 0) ^ 2 := by
  simp [integerTranslation, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two]
  ring

theorem cusp_conjugate_translation_mem_iff (N : ℕ) (r : SL(2, ℤ)) (k : ℤ) :
    r⁻¹ * integerTranslation k * r ∈ CongruenceSubgroup.Gamma0 N ↔
      (N : ℤ) ∣ k * (r 1 0) ^ 2 := by
  rw [CongruenceSubgroup.Gamma0_mem, cusp_conjugate_translation_lower,
    ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [neg_mul, dvd_neg]

theorem atkinPhase_int (k : ℤ) : atkinPhase (k : ℝ) = 1 := by
  unfold atkinPhase
  push_cast
  rw [mul_comm (2 * ↑Real.pi * Complex.I)]
  exact Complex.exp_int_mul_two_pi_mul_I k

theorem cuspFourierPhase_as_atkinPhase (w : ℝ) (n : ℤ) (x : ℝ) :
    cuspFourierPhase w n x = atkinPhase (-(n : ℝ) * x / w) := by
  unfold cuspFourierPhase cuspFourierFrequency atkinPhase
  congr 1
  push_cast
  ring

theorem cuspFourierPhase_integer_period_of_dvd (N : ℕ) [NeZero N]
    (n k : ℤ) (hNk : (N : ℤ) ∣ n * k) : cuspFourierPhase (N : ℝ) n (k : ℝ) = 1 := by
  obtain ⟨q,hq⟩ := hNk
  have hqr : (n : ℝ) * k = (N : ℝ) * q := by exact_mod_cast hq
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [cuspFourierPhase_as_atkinPhase]
  have he : -(n : ℝ) * k / N = -(q : ℝ) := by
    apply (div_eq_iff hN).mpr
    nlinarith
  rw [he]
  simpa only [Int.cast_neg] using atkinPhase_int (-q)

theorem cuspFourierPhase_integer_shift_of_dvd (N : ℕ) [NeZero N]
    (n k : ℤ) (hNk : (N : ℤ) ∣ n * k) (x : ℝ) :
    cuspFourierPhase (N : ℝ) n (x + k) = cuspFourierPhase (N : ℝ) n x := by
  rw [cuspFourierPhase_add, cuspFourierPhase_integer_period_of_dvd N n k hNk, mul_one]

end ArtinMatthews
