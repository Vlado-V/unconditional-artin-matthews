module

public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Generic real pole-kernel comparison, extracted unchanged from OpenAI
PrimePackets/HaarUniqueness.lean. -/
namespace OAI.PrimeDegreePackets
noncomputable section
open Filter
open scoped Topology

def realPoleKernel (X Y U : ℝ) : ℝ := (X+U) / ((X+U)^2+Y^2)

lemma realPoleKernel_nonneg {X Y U : ℝ} (hX : 0 ≤ X) (hU : 0 ≤ U) :
    0 ≤ realPoleKernel X Y U := by
  exact div_nonneg (add_nonneg hX hU) (add_nonneg (sq_nonneg _) (sq_nonneg _))

 

theorem realPoleKernel_comparison {c X Y U : ℝ} (hc : 0 < c)
    (hX : 0 ≤ X) (hU : 0 < U) (hU4 : U ≤ 4) (hgap : c^2 ≤ X^2+Y^2) :
    realPoleKernel X Y U ≤ 4*(1+3/c)^2 * realPoleKernel X Y 1 := by
  let q := (X+U)^2+Y^2
  let q₀ := (X+1)^2+Y^2
  have hcq : c^2 ≤ q := by dsimp [q]; nlinarith
  have hq : 0 < q := lt_of_lt_of_le (sq_pos_of_pos hc) hcq
  have hq₀ : 0 < q₀ := by dsimp [q₀]; nlinarith [sq_nonneg Y]
  have hs : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
  have hcs : c ≤ Real.sqrt q := by nlinarith
  have hAs : X+U ≤ Real.sqrt q := by
    have hqY : (X+U)^2 ≤ q := by dsimp [q]; nlinarith [sq_nonneg Y]
    nlinarith
  have hdiff : (1-U)^2 ≤ 9 := by nlinarith
  have hterm : 2*(X+U)*(1-U) ≤ 6*Real.sqrt q := by
    have h1 : 2*(X+U)*(1-U) ≤ 6*(X+U) := by nlinarith
    linarith
  have hq₀s : q₀ ≤ (Real.sqrt q+3)^2 := by
    have he : q₀ = q + 2*(X+U)*(1-U) + (1-U)^2 := by dsimp [q₀,q]; ring
    rw [he]
    nlinarith
  have hfactor : 0 < 1+3/c := by positivity
  have hscale : Real.sqrt q+3 ≤ (1+3/c)*Real.sqrt q := by
    have H := mul_le_mul_of_nonneg_left hcs (show 0 ≤ 3/c by positivity)
    have he : (3/c)*c = 3 := by field_simp
    rw [he] at H
    nlinarith
  have hratio : q₀ ≤ (1+3/c)^2*q := by
    calc
      q₀ ≤ (Real.sqrt q+3)^2 := hq₀s
      _ ≤ ((1+3/c)*Real.sqrt q)^2 := pow_le_pow_left₀ (by positivity) hscale 2
      _ = (1+3/c)^2*q := by rw [mul_pow,hsq]
  have hx : X+U ≤ 4*(X+1) := by linarith
  have hmul := mul_le_mul hx hratio hq₀.le (by linarith : 0 ≤ 4*(X+1))
  unfold realPoleKernel
  change (X+U)/q ≤ 4*(1+3/c)^2*((X+1)/q₀)
  rw [← mul_div_assoc,le_div_iff₀ hq₀,div_mul_eq_mul_div,div_le_iff₀ hq]
  nlinarith only [hmul]

 

theorem tsum_realPoleKernel_comparison {ι : Type*} {c U : ℝ}
    (X Y : ι → ℝ) (hc : 0 < c) (hX : ∀ i, 0 ≤ X i)
    (hU : 0 < U) (hU4 : U ≤ 4) (hgap : ∀ i, c^2 ≤ (X i)^2+(Y i)^2)
    (hs : Summable (fun i => realPoleKernel (X i) (Y i) 1)) :
    Summable (fun i => realPoleKernel (X i) (Y i) U) ∧
    0 ≤ ∑' i, realPoleKernel (X i) (Y i) U ∧
    (∑' i, realPoleKernel (X i) (Y i) U) ≤
      4*(1+3/c)^2 * (∑' i, realPoleKernel (X i) (Y i) 1) := by
  have hb (i : ι) := realPoleKernel_comparison hc (hX i) hU hU4 (hgap i)
  have hn (i : ι) := realPoleKernel_nonneg (Y := Y i) (hX i) hU.le
  have hsum := (hs.mul_left (4*(1+3/c)^2)).of_nonneg_of_le hn hb
  refine ⟨hsum,tsum_nonneg hn,?_⟩
  simpa only [tsum_mul_left] using hsum.tsum_le_tsum hb (hs.mul_left (4*(1+3/c)^2))

end
end OAI.PrimeDegreePackets
