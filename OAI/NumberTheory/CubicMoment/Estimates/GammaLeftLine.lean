module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
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

namespace OAI

/-! A far-left bound for the gamma quotient, obtained directly from
recurrence at half-integer real parts. No Stirling estimate is assumed. -/

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma half_sub_nat_regular (m : ℕ) (u : ℝ) :
    ∀ n : ℕ, ((1/2:ℂ)-(m:ℂ)+(u:ℂ)*Complex.I) ≠ -(n:ℂ) := by
  intro n h
  have hr := congrArg Complex.re h
  simp only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.natCast_re,
    Complex.neg_re,zero_mul,mul_zero,sub_zero,add_zero] at hr
  norm_num at hr
  have he : (2:ℝ)*m = 2*(n:ℝ)+1 := by linarith
  have hn : 2*m = 2*n+1 := by exact_mod_cast he
  omega

private lemma norm_ascPochhammer_le (n : ℕ) (z : ℂ) :
    ‖(ascPochhammer ℂ n).eval z‖ ≤ (‖z‖+(n:ℝ))^n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ascPochhammer_succ_eval,norm_mul]
      have hn : ‖z+(n:ℂ)‖ ≤ ‖z‖+(n:ℝ) := by
        simpa using norm_add_le z (n:ℂ)
      calc
        _ ≤ (‖z‖+(n:ℝ))^n * (‖z‖+(n:ℝ)) :=
          mul_le_mul ih hn (_root_.norm_nonneg _) (by positivity)
        _ = (‖z‖+(n:ℝ))^(n+1) := (pow_succ _ _).symm
        _ ≤ (‖z‖+((n+1:ℕ):ℝ))^(n+1) := by
          apply pow_le_pow_left₀ (by positivity)
          push_cast
          linarith

/-- The quotient on `Re s = 1/2-m` is a polynomial in norm of degree
`2m`, because the gamma arguments differ by the integer `2m` after
complex conjugation. -/
theorem norm_gamma_left_ratio_le (m : ℕ) (u : ℝ) :
    ‖Complex.Gamma ((1/2:ℂ)+(m:ℂ)-(u:ℂ)*Complex.I) /
      Complex.Gamma ((1/2:ℂ)-(m:ℂ)+(u:ℂ)*Complex.I)‖ ≤
        (3*(m:ℝ)+1)^(2*m)*(1+|u|)^(2*m) := by
  let z : ℂ := (1/2:ℂ)-(m:ℂ)+(u:ℂ)*Complex.I
  have he : ((1/2:ℂ)+(m:ℂ)-(u:ℂ)*Complex.I) =
      starRingEnd ℂ (z+(2*m:ℕ)) := by
    dsimp [z]
    simp only [map_add,map_sub,map_mul,Complex.conj_ofReal,Complex.conj_I,
      map_natCast,map_div₀,map_one,map_ofNat]
    push_cast
    ring
  have hq := Complex.Gamma_add_nat_div_Gamma_eq (n := 2*m) z (half_sub_nat_regular m u)
  have hn : ‖z‖ ≤ (m:ℝ)+1+|u| := by
    calc
      _ ≤ ‖(1/2:ℂ)-(m:ℂ)‖+‖(u:ℂ)*Complex.I‖ := norm_add_le _ _
      _ ≤ ‖(1/2:ℂ)‖+‖(m:ℂ)‖+‖(u:ℂ)*Complex.I‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ _ := by simp; linarith
  calc
    _ = ‖Complex.Gamma (z+(2*m:ℕ))/Complex.Gamma z‖ := by
      rw [he,Complex.Gamma_conj,norm_div,norm_div,Complex.norm_conj]
    _ = ‖(ascPochhammer ℂ (2*m)).eval z‖ := congrArg (fun w : ℂ => ‖w‖) hq
    _ ≤ (‖z‖+((2*m:ℕ):ℝ))^(2*m) := norm_ascPochhammer_le _ _
    _ ≤ ((3*(m:ℝ)+1)*(1+|u|))^(2*m) := by
      apply pow_le_pow_left₀ (by positivity)
      push_cast
      nlinarith [abs_nonneg u,show (0:ℝ) ≤ m by positivity]
    _ = _ := mul_pow _ _ _

end CubicFirstMoment

end

end OAI
