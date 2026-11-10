module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
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
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TotallySplit
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

/-! The conserved logarithmic energy on a cusp Euler ray. Actual finite
vertical derivative and weighted mass exclude both oscillating and threshold
constant modes on an infinite tail. -/
noncomputable section
open Set Filter MeasureTheory
namespace ArtinMatthews

def spectralRealEulerTailEnergy (l : ℝ) (c g : ℝ → ℝ) (y : ℝ) : ℝ :=
  ((y*g y-c y/2)^2+(l-1/4)*(c y)^2)/y

theorem spectralRealEulerTailEnergy_hasDerivAt (l : ℝ) (c g : ℝ → ℝ) {y : ℝ} (hy : 0<y)
    (hc : HasDerivAt c (g y) y) (hg : HasDerivAt g (-l*c y/y^2) y) :
    HasDerivAt (spectralRealEulerTailEnergy l c g) 0 y := by
  have hY := hasDerivAt_id' y
  have hV := ((hY.mul hg).sub (hc.div_const 2)).pow 2
  have hC := ((hc.pow 2).const_mul (l-1/4))
  convert (hV.add hC).div hY hy.ne' using 1
  · rfl
  · dsimp
    field_simp [hy.ne']
    ring

theorem spectralRealEulerTailEnergy_div_bound (l : ℝ) (hl : (1/4:ℝ)≤l)
    (c g : ℝ → ℝ) {y : ℝ} (hy : 0<y) :
    0 ≤ spectralRealEulerTailEnergy l c g y/y ∧
      spectralRealEulerTailEnergy l c g y/y ≤ 2*(g y)^2+(l+1/4)*((c y)^2/y^2) := by
  have hq : 0≤l-1/4 := sub_nonneg.mpr hl
  constructor
  · unfold spectralRealEulerTailEnergy
    positivity
  · have he : spectralRealEulerTailEnergy l c g y/y=
        (g y-c y/(2*y))^2+(l-1/4)*((c y)^2/y^2) := by
      unfold spectralRealEulerTailEnergy
      field_simp [hy.ne']
    have hb : (g y-c y/(2*y))^2≤2*(g y)^2+2*(c y/(2*y))^2 := by
      nlinarith [sq_nonneg (g y+c y/(2*y))]
    have hhalf : 2*(c y/(2*y))^2=((c y)^2/y^2)/2 := by ring
    rw [he]
    calc
      _ ≤ (2*(g y)^2+2*(c y/(2*y))^2)+(l-1/4)*((c y)^2/y^2) := add_le_add hb le_rfl
      _ = _ := by rw [hhalf]; ring

theorem spectralRealEulerTail_constant_div_eq_zero {Y a : ℝ} (hY : 0<Y)
    (hi : IntegrableOn (fun y : ℝ => a/y) (Ioi Y)) : a=0 := by
  by_contra ha
  have hi' : IntegrableOn (fun y : ℝ => a*y^(-1:ℝ)) (Ioi Y) := by
    apply hi.congr
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with y hy
    have hy0 := hY.trans hy
    rw [Real.rpow_neg hy0.le,Real.rpow_one,div_eq_mul_inv]
  have hpow := (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr ha) (fun y : ℝ => y^(-1:ℝ))).mp hi'
  exact (lt_irrefl (-1:ℝ)) ((integrableOn_Ioi_rpow_iff hY).mp hpow)

theorem spectralRealEulerTailEnergy_eq_zero {Y l : ℝ} (hY : 0<Y) (hl : (1/4:ℝ)≤l)
    (c g : ℝ → ℝ) (hc : ∀ y>Y,HasDerivAt c (g y) y)
    (hg : ∀ y>Y,HasDerivAt g (-l*c y/y^2) y)
    (hmc : IntegrableOn (fun y => (c y)^2/y^2) (Ioi Y))
    (hmg : IntegrableOn (fun y => (g y)^2) (Ioi Y)) :
    ∀ y>Y,spectralRealEulerTailEnergy l c g y=0 := by
  let E := spectralRealEulerTailEnergy l c g
  have hE (y : ℝ) (hy : y∈Ioi Y) : HasDerivAt E 0 y :=
    spectralRealEulerTailEnergy_hasDerivAt l c g (hY.trans hy) (hc y hy) (hg y hy)
  have hconst (x y : ℝ) (hx : Y<x) (hy : Y<y) : E x=E y :=
    isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi Y).isPreconnected
      (fun z hz => (hE z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hE z hz).deriv) hx hy
  have hInt : IntegrableOn (fun y => E y/y) (Ioi Y) := by
    have hCont : ContinuousOn (fun y => E y/y) (Ioi Y) :=
      (fun y hy => ((hE y hy).div (hasDerivAt_id' y) (hY.trans hy).ne').continuousAt.continuousWithinAt)
    apply ((hmg.const_mul 2).add (hmc.const_mul (l+1/4))).mono'
      (hCont.aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with y hy
    have hB := spectralRealEulerTailEnergy_div_bound l hl c g (hY.trans hy)
    change ‖E y/y‖≤2*(g y)^2+(l+1/4)*((c y)^2/y^2)
    rw [Real.norm_eq_abs,abs_of_nonneg hB.1]
    exact hB.2
  intro y hy
  apply spectralRealEulerTail_constant_div_eq_zero hY
  apply hInt.congr
  filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with z hz
  exact congrArg (fun q : ℝ => q/z) (hconst z y hz hy)

theorem spectralRealEulerTail_eq_zero {Y l : ℝ} (hY : 0<Y) (hl : (1/4:ℝ)≤l)
    (c g : ℝ → ℝ) (hc : ∀ y>Y,HasDerivAt c (g y) y)
    (hg : ∀ y>Y,HasDerivAt g (-l*c y/y^2) y)
    (hmc : IntegrableOn (fun y => (c y)^2/y^2) (Ioi Y))
    (hmg : IntegrableOn (fun y => (g y)^2) (Ioi Y)) : ∀ y>Y,c y=0 := by
  have hEnergy := spectralRealEulerTailEnergy_eq_zero hY hl c g hc hg hmc hmg
  have hRel (y : ℝ) (hy : Y<y) : y*g y=c y/2 := by
    have he := hEnergy y hy
    unfold spectralRealEulerTailEnergy at he
    have hn := (div_eq_zero_iff.mp he).resolve_right (hY.trans hy).ne'
    have hpos : 0≤(l-1/4)*(c y)^2 := mul_nonneg (sub_nonneg.mpr hl) (sq_nonneg _)
    have hs : (y*g y-c y/2)^2=0 := le_antisymm (by linarith) (sq_nonneg _)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
  let H := fun y => c y/Real.sqrt y
  have hH (y : ℝ) (hy : y∈Ioi Y) : HasDerivAt H 0 y := by
    have hy0 := hY.trans hy
    have hs := (Real.sqrt_pos.mpr hy0).ne'
    convert (hc y hy).div (Real.hasDerivAt_sqrt hy0.ne') hs using 1
    have hS := Real.sq_sqrt hy0.le
    have h := hRel y hy
    field_simp [hs]
    rw [hS]
    nlinarith
  have hconst (x y : ℝ) (hx : Y<x) (hy : Y<y) : H x=H y :=
    isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi Y).isPreconnected
      (fun z hz => (hH z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hH z hz).deriv) hx hy
  intro y hy
  have hz : (H y)^2=0 := by
    apply spectralRealEulerTail_constant_div_eq_zero hY
    apply hmc.congr
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with z hz
    have hz0 := hY.trans hz
    rw [← hconst z y hz hy]
    change (c z)^2/z^2=(c z/Real.sqrt z)^2/z
    rw [div_pow,Real.sq_sqrt hz0.le]
    ring
  exact (div_eq_zero_iff.mp (sq_eq_zero_iff.mp hz)).resolve_right (Real.sqrt_pos.mpr (hY.trans hy)).ne'

end ArtinMatthews
