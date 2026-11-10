module

public import ArtinMatthews.SpectralBesselJOrderZeroDerivative
public import ArtinMatthews.SpectralWeylMultipliers
public import ArtinMatthews.SpectralWeylGaussianJImaginary
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

/-! The divided J multiplier has a genuine removable order-zero limit.
The value is -8 times the proved order derivative divided by X, with the
literal Weyl normalization; its log-Poisson evaluation is inherited. -/

noncomputable section
open Set Filter
open scoped Topology

namespace ArtinMatthews

def spectralWeylJZeroMultiplier (X : ℝ) : ℂ :=
  -8*spectralBesselJOrderDerivativeZero X/(X : ℂ)

theorem spectralWeylJ_divided_order_zero_limit {X : ℝ} (hX : 0 < X) :
    Tendsto (fun ν : ℂ => (-(2 : ℂ)*(Real.pi : ℂ)/Complex.sin ((Real.pi : ℂ)*ν))*
      (Complex.besselJ (2*ν) (X : ℂ)-Complex.besselJ (2*(-ν)) (X : ℂ))/(X : ℂ))
      (𝓝[≠] (0 : ℂ)) (𝓝 (spectralWeylJZeroMultiplier X)) := by
  let D := spectralBesselJOrderDerivativeZero X
  let N : ℂ → ℂ := fun ν => Complex.besselJ (2*ν) (X : ℂ)-Complex.besselJ (2*(-ν)) (X : ℂ)
  let S : ℂ → ℂ := fun ν => Complex.sin ((Real.pi : ℂ)*ν)
  have hJ : HasDerivAt (fun ν : ℂ => Complex.besselJ ν (X : ℂ)) D 0 :=
    spectral_besselJ_order_hasDerivAt_zero hX
  have hplus : HasDerivAt (fun ν : ℂ => Complex.besselJ (2*ν) (X : ℂ)) (D*2) 0 := by
    simpa only [Function.comp_def,id_eq,mul_one] using
      hJ.comp_of_eq (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).const_mul 2) (by simp)
  have hminus : HasDerivAt (fun ν : ℂ => Complex.besselJ (2*(-ν)) (X : ℂ)) (D*(2*(-1))) 0 := by
    simpa only [Function.comp_def,Pi.neg_apply,id_eq] using!
      hJ.comp_of_eq (0 : ℂ) (((hasDerivAt_id (0 : ℂ)).neg).const_mul 2) (by simp)
  have hN : HasDerivAt N (4*D) 0 := by
    convert! hplus.sub hminus using 1
    ring_nf
  have hS : HasDerivAt S (Real.pi : ℂ) 0 := by
    simpa only [S,Function.comp_def,id_eq,mul_one,Complex.cos_zero,one_mul] using
      (Complex.hasDerivAt_sin (0 : ℂ)).comp_of_eq (0 : ℂ)
        ((hasDerivAt_id (0 : ℂ)).const_mul (Real.pi : ℂ)) (by simp)
  have hN₀ : N 0 = 0 := by simp [N]
  have hS₀ : S 0 = 0 := by simp [S]
  have hn : Tendsto (fun ν : ℂ => N ν/ν) (𝓝[≠] (0 : ℂ)) (𝓝 (4*D)) := by
    simpa only [zero_add,hN₀,sub_zero,smul_eq_mul,div_eq_mul_inv,mul_comm] using hN.tendsto_slope_zero
  have hs : Tendsto (fun ν : ℂ => S ν/ν) (𝓝[≠] (0 : ℂ)) (𝓝 (Real.pi : ℂ)) := by
    simpa only [zero_add,hS₀,sub_zero,smul_eq_mul,div_eq_mul_inv,mul_comm] using hS.tendsto_slope_zero
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hRatio : Tendsto (fun ν : ℂ => N ν/S ν) (𝓝[≠] (0 : ℂ)) (𝓝 ((4*D)/(Real.pi : ℂ))) := by
    apply (hn.div hs hπ).congr'
    filter_upwards [self_mem_nhdsWithin] with ν hν
    exact div_div_div_cancel_right₀ (show ν ≠ 0 from hν) (N ν) (S ν)
  have hscale : (-(2 : ℂ)*(Real.pi : ℂ))*((4*D)/(Real.pi : ℂ))/(X : ℂ) = spectralWeylJZeroMultiplier X := by
    unfold spectralWeylJZeroMultiplier
    change _ = -8*D/(X : ℂ)
    field_simp [hπ,Complex.ofReal_ne_zero.mpr hX.ne']
    ring_nf
  have he : (fun ν : ℂ => (-(2 : ℂ)*(Real.pi : ℂ)/Complex.sin ((Real.pi : ℂ)*ν))*
      (Complex.besselJ (2*ν) (X : ℂ)-Complex.besselJ (2*(-ν)) (X : ℂ))/(X : ℂ)) =
      fun ν : ℂ => (-(2 : ℂ)*(Real.pi : ℂ))*(N ν/S ν)/(X : ℂ) := by
    funext ν
    dsimp [N,S]
    ring_nf
  rw [he,← hscale]
  exact (tendsto_const_nhds.mul hRatio).div_const _

theorem spectralWeylJMultiplier_tendsto_zero_right {X : ℝ} (hX : 0 < X) :
    Tendsto (fun r : ℝ => spectralWeylJMultiplier r X) (𝓝[>] (0 : ℝ))
      (𝓝 (spectralWeylJZeroMultiplier X)) := by
  have hp : Tendsto (fun r : ℝ => (r : ℂ)*Complex.I) (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hc : Continuous (fun r : ℝ => (r : ℂ)*Complex.I) := Complex.continuous_ofReal.mul continuous_const
      simpa only [Complex.ofReal_zero,zero_mul] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      change (r : ℂ)*Complex.I ≠ 0
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (show 0 < r from hr).ne') Complex.I_ne_zero
  apply ((spectralWeylJ_divided_order_zero_limit hX).comp hp).congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  change 0 < r at hr
  change (-(2 : ℂ)*(Real.pi : ℂ)/Complex.sin ((Real.pi : ℂ)*((r : ℂ)*Complex.I)))*
    (Complex.besselJ (2*((r : ℂ)*Complex.I)) (X : ℂ)-
      Complex.besselJ (2*(-((r : ℂ)*Complex.I))) (X : ℂ))/(X : ℂ) = spectralWeylJMultiplier r X
  rw [spectralWeylJMultiplier,ite_eq_left hX,spectralWeylJMultiplier_imaginary_coefficient hr,
    show (((2*r : ℝ) : ℂ)*Complex.I) = 2*((r : ℂ)*Complex.I) by push_cast; ring,
    show (((-2*r : ℝ) : ℂ)*Complex.I) = 2*(-((r : ℂ)*Complex.I)) by push_cast; ring]

end ArtinMatthews
