module

public import ArtinMatthews.MarkedMajorArcProductPolynomial
public import ArtinMatthews.MarkedMajorArcCenteredCoefficient
public import Mathlib.Analysis.CStarAlgebra.Classes
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

/-! Literal coefficient bounds and phase identities used by the product
mean-square estimate for the centered long polynomial. -/
namespace ArtinMatthews
open Finset

lemma marked_nat_cpow_eq_phase {n : ℕ} (hn : 0 < n) (t : ℝ) :
    (n:ℂ)^((t:ℂ)*Complex.I) = markedPrimePhase n t := by
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Complex.cpow_def_of_ne_zero hnC,← Complex.natCast_log]
  unfold markedPrimePhase
  congr 1
  push_cast
  ring

 theorem marked_centered_coefficient_norm_le (W modulation : ℝ) {n : ℕ}
    (hn : 0 < n) (hlog : 1 ≤ Real.log n) :
    ‖markedMajorCenteredCoefficient W modulation n‖ ≤ 1+(markedSieveEulerProduct W)⁻¹ := by
  classical
  have hV := markedSieveEulerProduct_pos W
  have hlog0 : 0 < Real.log n := zero_lt_one.trans_le hlog
  have hloginv : (Real.log n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hlog
  unfold markedMajorCenteredCoefficient
  rw [norm_mul,marked_nat_cpow_eq_phase hn,markedPrimePhase_norm,one_mul]
  have h1 : ‖if n.Prime then (1:ℂ) else 0‖ ≤ 1 := by split_ifs <;> norm_num
  have h2 : ‖(markedSieveEulerProduct W:ℂ)⁻¹*((Real.log n)⁻¹:ℝ)*
      (if ∀ p ∈ Nat.primesLE ⌊W⌋₊, ¬p∣n then (1:ℂ) else 0)‖ ≤ (markedSieveEulerProduct W)⁻¹ := by
    split_ifs
    · simp only [mul_one,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos hV,abs_of_pos hlog0]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hloginv (inv_nonneg.mpr hV.le)
    · simp only [mul_zero,norm_zero]
      positivity
  exact (norm_sub_le _ _).trans (add_le_add h1 h2)

 theorem marked_centered_sum_eq_natural {q : ℕ} (χ : DirichletCharacter ℂ q)
    (W modulation t H u v : ℝ) :
    markedMajorCenteredSum χ W modulation t H u v =
      markedNaturalPolynomial (Ioc ⌊u⌋₊ ⌊v⌋₊)
        (fun n => (H:ℂ)⁻¹*(markedMajorCenteredCoefficient W modulation n*χ (n:ZMod q))) t := by
  unfold markedMajorCenteredSum markedNaturalPolynomial
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  rw [marked_nat_cpow_eq_phase (by have := (mem_Ioc.mp hn).1; omega)]
  ring

 theorem marked_centered_sum_continuous {q : ℕ} (χ : DirichletCharacter ℂ q)
    (W modulation H u v : ℝ) :
    Continuous (fun t => markedMajorCenteredSum χ W modulation t H u v) := by
  simp_rw [marked_centered_sum_eq_natural]
  unfold markedNaturalPolynomial markedPrimePhase
  fun_prop

 theorem marked_centered_normalized_coefficient_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    (W modulation : ℝ) {H u v : ℝ} (hH : 0 < H) (hu : 0 < u) (hlog : 1 ≤ Real.log u)
    (n : ℕ) (hn : n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊) :
    ‖(H:ℂ)⁻¹*(markedMajorCenteredCoefficient W modulation n*χ (n:ZMod q))‖ ≤
      (1+(markedSieveEulerProduct W)⁻¹)/H := by
  have hun : u < n := (Nat.floor_lt hu.le).mp (mem_Ioc.mp hn).1
  have hnpos : 0 < n := by exact_mod_cast hu.trans hun
  have hnlog : 1 ≤ Real.log n := hlog.trans (Real.log_le_log hu hun.le)
  rw [norm_mul,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hH]
  have hV := markedSieveEulerProduct_pos W
  have hb := mul_le_mul (marked_centered_coefficient_norm_le W modulation hnpos hnlog)
    (χ.norm_le_one (n:ZMod q)) (norm_nonneg _) (by positivity : 0 ≤ 1+(markedSieveEulerProduct W)⁻¹)
  have hh := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hH.le)
  simpa only [mul_one,one_mul,div_eq_mul_inv,mul_comm] using hh

end ArtinMatthews
