module

public import ArtinMatthews.SpectralWeylDimensionlessKernel
public import ArtinMatthews.SpectralWeylTwoHeightKernel
public import ArtinMatthews.SpectralWeylDimensionlessDensity
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Literal frequency dilation of the actual Weyl density. The phase
signs and the factor sqrt(a*b)/C^2 are retained. -/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

theorem spectralWeylDimensionlessKernel_scale {a b x z X : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) (hz : 0 < z)
    (hX : 2*Real.sqrt (x*z) < X) (s t : ℝ) :
    spectralWeylDimensionlessKernel s t X x z =
      Real.sqrt (a*b)*spectralWeylDimensionlessKernel (s/a) (t/b)
        (Real.sqrt (a*b)*X) (a*x) (b*z) := by
  have hab : 0 < a*b := mul_pos ha hb
  have hxz : 0 < x*z := mul_pos hx hz
  have hR : 0 < Real.sqrt (a*b) := Real.sqrt_pos.mpr hab
  have hroot : Real.sqrt ((a*x)*(b*z)) = Real.sqrt (a*b)*Real.sqrt (x*z) := by
    rw [show (a*x)*(b*z) = (a*b)*(x*z) by ring,Real.sqrt_mul hab.le]
  have hX' : 2*Real.sqrt ((a*x)*(b*z)) < Real.sqrt (a*b)*X := by
    rw [hroot]
    nlinarith [mul_lt_mul_of_pos_left hX hR]
  have hR2 : Real.sqrt (a*b)^2 = a*b := Real.sq_sqrt hab.le
  have hd : 0 < X^2/4-x*z := by
    have hX0 : 0 < X := (mul_pos two_pos (Real.sqrt_pos.mpr hxz)).trans hX
    have hp := mul_pos (sub_pos.mpr hX) (add_pos hX0 (mul_pos two_pos (Real.sqrt_pos.mpr hxz)))
    nlinarith [Real.sq_sqrt hxz.le]
  have harg : (Real.sqrt (a*b)*X)^2/(4*(a*x)*(b*z))-1 = X^2/(4*x*z)-1 := by
    rw [mul_pow,hR2]
    field_simp
  have hden : Real.sqrt ((Real.sqrt (a*b)*X)^2/4-(a*x)*(b*z)) =
      Real.sqrt (a*b)*Real.sqrt (X^2/4-x*z) := by
    rw [mul_pow,hR2,show (a*b)*X^2/4-(a*x)*(b*z) = (a*b)*(X^2/4-x*z) by ring,
      Real.sqrt_mul hab.le]
  rw [spectralWeylDimensionlessKernel_eq hx hz hX,
    spectralWeylDimensionlessKernel_eq (mul_pos ha hx) (mul_pos hb hz) hX',harg,hden]
  rw [show s/a*(a*x)+t/b*(b*z) = s*x+t*z by field_simp]
  field_simp

theorem weylTwoHeightDensity_frequency_scaled (N : ℕ) [NeZero N] (m n : ℤ)
    (ρ η : ℝ → ℝ) {a b C y v : ℝ} (ha : 0 < a) (hb : 0 < b) (hC : 0 < C) (hy : 0 < y)
    (hv : v ∈ Ioo 0 (1/(C^2*y))) :
    weylTwoHeightDensity N m n ρ η C y v =
      (((ρ y*Real.sqrt y/y)*(η v*Real.sqrt v/v)*Real.sqrt (a*b)/(C^2*y*v))*
        spectralWeylDimensionlessKernel
          (cuspFourierFrequency (N : ℝ) m/a) (cuspFourierFrequency (N : ℝ) n/b)
          (Real.sqrt (a*b)*(2/C)) (a*y) (b*v) : ℝ) := by
  have hv0 : 0 < v := hv.1
  have hp : 0 < C^2*y := by positivity
  have hsmall : y*v < (1/C)^2 := by
    rw [div_pow,one_pow]
    apply (lt_div_iff₀ (sq_pos_of_pos hC)).mpr
    have hh := (lt_div_iff₀ hp).mp hv.2
    nlinarith
  have hX : 2*Real.sqrt (y*v) < 2/C := by
    have hh := (Real.sqrt_lt' (one_div_pos.mpr hC)).mpr hsmall
    calc
      _ < 2*(1/C) := mul_lt_mul_of_pos_left hh two_pos
      _ = _ := by ring
  rw [weylTwoHeightDensity_dimensionless N m n ρ η hC hy hv,
    spectralWeylDimensionlessKernel_scale ha hb hy hv0 hX]
  congr 1
  ring

end ArtinMatthews
