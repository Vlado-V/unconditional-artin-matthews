module

public import ArtinMatthews.MarkedPhysicalMomentTube
public import ArtinMatthews.MarkedMemoryOrphanParameterBounds
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite tube radius and path count have an explicit
exponential-in-logarithm budget at the original moment length. The
source bound on d0*Y keeps its exponent 21/100. -/
namespace ArtinMatthews
noncomputable section

def markedPhysicalCoordinateTubeCost (K A : ℝ) : ℝ :=
  8*(35+1024*K)+32+8*A

theorem markedPhysicalMomentTube_width_bound {x : ℝ} (hlog : 1 ≤ Real.log x)
    (n : ℕ) {K H A : ℝ} (hK : 0 ≤ K) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hHhi : H ≤ Real.exp (A*(Real.log x)^(21/100:ℝ))) :
    2*(markedPhysicalMomentTubeRadius n K H:ℝ)+1 ≤
      Real.exp ((35+1024*K)+((n:ℝ)+1)+A*(Real.log x)^(21/100:ℝ)) := by
  have hL : 0 ≤ Real.log x := by linarith
  have he : 1 ≤ Real.exp (A*(Real.log x)^(21/100:ℝ)) :=
    Real.one_le_exp (mul_nonneg hA (Real.rpow_nonneg hL _))
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 16+512*(n:ℝ)*K*H by positivity)
  have hwidth : 2*(markedPhysicalMomentTubeRadius n K H:ℝ)+1 ≤ 35+1024*(n:ℝ)*K*H := by
    unfold markedPhysicalMomentTubeRadius
    linarith
  have hfirst : 35 ≤ 35*((n:ℝ)+1)*Real.exp (A*(Real.log x)^(21/100:ℝ)) := by
    have h1 := mul_le_mul_of_nonneg_right
      (show (1:ℝ) ≤ (n:ℝ)+1 by have hn := Nat.cast_nonneg n (α := ℝ); linarith) (zero_le_one.trans he)
    nlinarith
  have hsecond : 1024*(n:ℝ)*K*H ≤
      1024*K*((n:ℝ)+1)*Real.exp (A*(Real.log x)^(21/100:ℝ)) := by
    have h1 := mul_le_mul_of_nonneg_left hHhi (show 0 ≤ 1024*(n:ℝ)*K by positivity)
    have h2 := mul_le_mul_of_nonneg_right (show (n:ℝ) ≤ (n:ℝ)+1 by linarith)
      (show 0 ≤ 1024*K*Real.exp (A*(Real.log x)^(21/100:ℝ)) by positivity)
    nlinarith
  have hC : 0 ≤ 35+1024*K := by positivity
  have hCexp : 35+1024*K ≤ Real.exp (35+1024*K) := by
    linarith [Real.add_one_le_exp (35+1024*K)]
  have hnexp : (n:ℝ)+1 ≤ Real.exp ((n:ℝ)+1) := by linarith [Real.add_one_le_exp ((n:ℝ)+1)]
  calc
    _ ≤ 35+1024*(n:ℝ)*K*H := hwidth
    _ ≤ (35+1024*K)*((n:ℝ)+1)*Real.exp (A*(Real.log x)^(21/100:ℝ)) := by nlinarith
    _ ≤ Real.exp (35+1024*K)*Real.exp ((n:ℝ)+1)*Real.exp (A*(Real.log x)^(21/100:ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul hCexp hnexp (by positivity) (Real.exp_nonneg _)) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add,← Real.exp_add]

theorem markedPhysicalMomentTube_path_budget {x : ℝ} (hlog : 1 ≤ Real.log x)
    {K H A : ℝ} (hK : 0 ≤ K) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hHhi : H ≤ Real.exp (A*(Real.log x)^(21/100:ℝ))) :
    (2*(markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K H:ℝ)+1)^(2*markedMemoryMomentLength x) ≤
      Real.exp (markedPhysicalCoordinateTubeCost K A*Real.log x) := by
  let n := markedMemoryMomentLength x
  let C := 35+1024*K
  have hL : 0 < Real.log x := by linarith
  have hN := (markedMemoryMomentLength_sqrt_bound hlog).1
  have hNlin : (n:ℝ) ≤ 4*Real.log x := by
    have hp : (Real.log x)^(1/2:ℝ) ≤ Real.log x := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hlog (by norm_num : (1/2:ℝ) ≤ 1)
    dsimp only [n]
    linarith
  have hNN : (n:ℝ)*((n:ℝ)+1) ≤ 16*Real.log x := by
    have hs := markedMemoryMomentLength_sq_bound hlog
    dsimp only [n]
    nlinarith [Nat.cast_nonneg (markedMemoryMomentLength x) (α := ℝ)]
  have hNpow : (n:ℝ)*(Real.log x)^(21/100:ℝ) ≤ 4*Real.log x := by
    have hmul := mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg hL.le (21/100:ℝ))
    have heq : (Real.log x)^(1/2:ℝ)*(Real.log x)^(21/100:ℝ)=(Real.log x)^(71/100:ℝ) := by
      rw [← Real.rpow_add hL]
      norm_num
    have hpow : (Real.log x)^(71/100:ℝ) ≤ Real.log x := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hlog (by norm_num : (71/100:ℝ) ≤ 1)
    dsimp only [n]
    nlinarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcost : (2*(n:ℝ))*(C+((n:ℝ)+1)+A*(Real.log x)^(21/100:ℝ)) ≤
      markedPhysicalCoordinateTubeCost K A*Real.log x := by
    have hc := mul_le_mul_of_nonneg_left hNlin (show 0 ≤ 2*C by positivity)
    have hn := mul_le_mul_of_nonneg_left hNN (by norm_num : (0:ℝ) ≤ 2)
    have hp := mul_le_mul_of_nonneg_left hNpow (show 0 ≤ 2*A by positivity)
    dsimp only [markedPhysicalCoordinateTubeCost,C] at *
    nlinarith
  calc
    _ ≤ (Real.exp (C+((n:ℝ)+1)+A*(Real.log x)^(21/100:ℝ)))^(2*n) :=
      pow_le_pow_left₀ (by positivity) (markedPhysicalMomentTube_width_bound hlog n hK hH hA hHhi) (2*n)
    _ = Real.exp ((2*(n:ℝ))*(C+((n:ℝ)+1)+A*(Real.log x)^(21/100:ℝ))) := by
      rw [← Real.exp_nat_mul]
      push_cast
      rfl
    _ ≤ _ := Real.exp_le_exp.mpr hcost

end
end ArtinMatthews
