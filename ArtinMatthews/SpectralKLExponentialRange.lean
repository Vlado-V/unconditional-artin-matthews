module

public import ArtinMatthews.SpectralKLCompletedSynthesis
public import ArtinMatthews.SpectralKLCoshDifferenceRange
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Arcosh
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

/-! Ordinary exponential differences in the actual synthesis range,
including the positive anchor used for the subsequent density argument. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

def spectralKLExponentialDifference (a b x : ℝ) : ℂ :=
  Complex.exp (-(a*x) : ℝ)-Complex.exp (-(b*x) : ℝ)

theorem spectralKLExponentialDifference_memLp (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    MemLp (spectralKLExponentialDifference a b) 2 spectralKLPhysicalMeasure := by
  have heq : (fun x : ℝ => Complex.exp (-(x*Real.cosh (Real.arcosh a)) : ℝ)-
      Complex.exp (-(x*Real.cosh (Real.arcosh b)) : ℝ)) = spectralKLExponentialDifference a b := by
    funext x
    simp only [Real.cosh_arcosh ha,Real.cosh_arcosh hb,spectralKLExponentialDifference,mul_comm]
  simpa only [heq] using spectralKLCoshDifference_memLp (Real.arcosh a) (Real.arcosh b)

theorem spectralKLExponentialDifference_mem_range (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (spectralKLExponentialDifference_memLp a b ha hb).toLp (spectralKLExponentialDifference a b) ∈
      Set.range spectralKLCompletedSynthesis := by
  have heq : (fun x : ℝ => Complex.exp (-(x*Real.cosh (Real.arcosh a)) : ℝ)-
      Complex.exp (-(x*Real.cosh (Real.arcosh b)) : ℝ)) = spectralKLExponentialDifference a b := by
    funext x
    simp only [Real.cosh_arcosh ha,Real.cosh_arcosh hb,spectralKLExponentialDifference,mul_comm]
  simpa only [heq] using spectralKLCoshDifference_mem_range (Real.arcosh a) (Real.arcosh b)

def spectralKLExponentialAnchor (x : ℝ) : ℝ := Real.exp (-x)-Real.exp (-2*x)

theorem spectralKLExponentialAnchor_pos {x : ℝ} (hx : 0 < x) :
    0 < spectralKLExponentialAnchor x := by
  unfold spectralKLExponentialAnchor
  exact sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))

theorem spectralKLExponentialAnchor_memLp :
    MemLp (fun x : ℝ => (spectralKLExponentialAnchor x : ℂ)) 2 spectralKLPhysicalMeasure := by
  have heq : spectralKLExponentialDifference 1 2 = (fun x : ℝ => (spectralKLExponentialAnchor x : ℂ)) := by
    funext x
    simp only [spectralKLExponentialDifference,spectralKLExponentialAnchor,one_mul,
      Complex.ofReal_sub,Complex.ofReal_exp,neg_mul]
  simpa only [heq] using spectralKLExponentialDifference_memLp 1 2 le_rfl (by norm_num)

theorem spectralKLExponentialAnchor_square_integrable :
    Integrable (fun x : ℝ => (spectralKLExponentialAnchor x)^2) spectralKLPhysicalMeasure := by
  have hi := (memLp_two_iff_integrable_sq_norm spectralKLExponentialAnchor_memLp.aestronglyMeasurable).mp
    spectralKLExponentialAnchor_memLp
  apply hi.congr
  filter_upwards with x
  rw [Complex.norm_real,Real.norm_eq_abs,sq_abs]

theorem spectralKLExponentialAnchor_monomial (n : ℕ) (x : ℝ) :
    ((spectralKLExponentialAnchor x*(Real.exp (-x))^n : ℝ) : ℂ) =
      spectralKLExponentialDifference ((n : ℝ)+1) ((n : ℝ)+2) x := by
  unfold spectralKLExponentialAnchor spectralKLExponentialDifference
  rw [← Real.exp_nat_mul]
  rw [sub_mul,← Real.exp_add,← Real.exp_add]
  have h1 : -x+(n : ℝ)*(-x) = -(((n : ℝ)+1)*x) := by ring
  have h2 : -2*x+(n : ℝ)*(-x) = -(((n : ℝ)+2)*x) := by ring
  rw [h1,h2]
  simp only [Complex.ofReal_sub,Complex.ofReal_exp]

end ArtinMatthews
