module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import OAI.NumberTheory.EgyptianFractions.DiscreteFirstDerivative
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-! # A first-derivative bound for short logarithmic phase sums -/
namespace JointDickman
open Finset Problem337

lemma log_step_bounds {x : ℝ} (hx : 0 < x) :
    1/(x+1) ≤ Real.log (x+1)-Real.log x ∧
      Real.log (x+1)-Real.log x ≤ 1/x := by
  have hx1 : 0 < x+1 := by positivity
  rw [← Real.log_div hx1.ne' hx.ne']
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos (div_pos hx1 hx)
    convert h using 1
    field_simp
    ring
  · have h := Real.log_le_sub_one_of_pos (div_pos hx1 hx)
    convert h using 1
    field_simp
    ring

lemma log_step_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Real.log (y+1)-Real.log y ≤ Real.log (x+1)-Real.log x := by
  have hy : 0 < y := hx.trans_le hxy
  rw [← Real.log_div (by positivity : x+1 ≠ 0) hx.ne',
    ← Real.log_div (by positivity : y+1 ≠ 0) hy.ne']
  apply Real.log_le_log (by positivity)
  apply (div_le_div_iff₀ hy hx).mpr
  nlinarith

/-- Below the first stationary range the sharp logarithmic sum is bounded
by the reciprocal frequency, with no length-dependent error. -/
theorem positive_log_phase_first_bound {U Z : ℝ} (hU : 1 ≤ U)
    (hZ : 0 < Z) (hZU : Z ≤ U/4) (L R : ℕ)
    (hL : U ≤ (L:ℝ)) (hR : (R:ℝ) ≤ 2*U) :
    ‖∑ n ∈ Icc L R, ExponentialSum.phase (Z*Real.log (n:ℝ))‖ ≤ 8*U/Z := by
  have hU0 : 0 < U := by linarith
  have hβ : 0 < Z/(4*U) := by positivity
  have hd (i : ℕ) (hiL : L ≤ i) (hiR : i ≤ R) :
      Z/(4*U) ≤ Z*Real.log ((i+1:ℕ):ℝ)-Z*Real.log (i:ℝ) ∧
      Z*Real.log ((i+1:ℕ):ℝ)-Z*Real.log (i:ℝ) ≤ 1-Z/(4*U) := by
    have hi : U ≤ (i:ℝ) := hL.trans (by exact_mod_cast hiL)
    have hi2 : (i:ℝ) ≤ 2*U := (by exact_mod_cast hiR : (i:ℝ) ≤ R).trans hR
    have hi0 : (0:ℝ) < i := hU0.trans_le hi
    obtain ⟨hlo,hhi⟩ := log_step_bounds hi0
    push_cast
    rw [← mul_sub]
    constructor
    · apply (div_le_div_of_nonneg_left hZ.le (by positivity : (0:ℝ) < i+1)
        (by linarith : (i:ℝ)+1 ≤ 4*U)).trans
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hlo hZ.le
    · have hu : Z*((1:ℝ)/i) ≤ Z/U := by
        rw [mul_one_div]
        exact div_le_div_of_nonneg_left hZ.le hU0 hi
      have hh : Z/U ≤ 1/4 := (div_le_iff₀ hU0).mpr (by linarith)
      have hb : Z/(4*U) ≤ 1/4 := (div_le_iff₀ (by positivity)).mpr (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left hhi hZ.le]
  have hmono : AntitoneOn (fun i : ℕ => Z*Real.log ((i+1:ℕ):ℝ)-
      Z*Real.log (i:ℝ)) (Set.Icc L R) := by
    intro i hi j _ hij
    push_cast
    rw [← mul_sub, ← mul_sub]
    apply mul_le_mul_of_nonneg_left _ hZ.le
    exact log_step_antitone (hU0.trans_le (hL.trans (by exact_mod_cast hi.1)))
      (by exact_mod_cast hij)
  have hh := ExponentialSum.first_derivative_sum_bound_Icc
    (fun n => Z*Real.log (n:ℝ)) L R (Z/(4*U)) 0 hβ
    (fun i hiL hiR => by simpa using (hd i hiL hiR).1)
    (fun i hiL hiR => by simpa using (hd i hiL hiR).2) (Or.inr hmono)
  convert hh using 1
  field_simp
  norm_num

end JointDickman

end OAI
