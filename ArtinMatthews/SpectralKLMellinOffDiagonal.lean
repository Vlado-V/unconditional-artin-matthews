module

public import OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicSpace
public import ArtinMatthews.SpectralBesselProductClosed
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

/-! A genuine first KL boundary consequence: off the two spectral diagonals,
the Mellin-regularized K product tends to zero.  This pointwise limit is not
the distributional delta or spectral completeness theorem. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein
open scoped Topology

namespace ArtinMatthews

def spectralKProductClosedValue (ν μ z : ℂ) : ℂ :=
  ((2 : ℂ)^(z-3) * Complex.Gamma ((z-ν-μ)/2) * Complex.Gamma ((z+ν-μ)/2) *
    Complex.Gamma ((z-ν+μ)/2) * Complex.Gamma ((z+ν+μ)/2)) / Complex.Gamma z

theorem spectral_Gamma_continuousAt_imaginary {z : ℂ} (hz : z.re = 0) (hn : z ≠ 0) :
    ContinuousAt Complex.Gamma z := by
  apply Complex.continuousAt_Gamma z
  intro m hm
  have hr := congrArg Complex.re hm
  simp only [hz,Complex.neg_re,Complex.natCast_re] at hr
  have hm0 : m = 0 := by exact_mod_cast (neg_eq_zero.mp hr.symm)
  apply hn
  simpa only [hm0,Nat.cast_zero,neg_zero] using hm

theorem spectralKProductClosedValue_continuousAt_zero (ν μ : ℂ)
    (hν : ν.re = 0) (hμ : μ.re = 0) (hplus : ν+μ ≠ 0) (hminus : ν-μ ≠ 0) :
    ContinuousAt (spectralKProductClosedValue ν μ) 0 := by
  have hG (v : ℂ) (hv : v.re = 0) (hn : v ≠ 0) :
      ContinuousAt (fun z : ℂ => Complex.Gamma ((z+v)/2)) 0 := by
    have hvg : (v/2).re = 0 := by simp only [Complex.div_ofNat_re,hv,zero_div]
    have hvn : v/2 ≠ 0 := div_ne_zero hn (by norm_num)
    simpa only [Function.comp_def] using
      (spectral_Gamma_continuousAt_imaginary hvg hvn).comp_of_eq
        (show ContinuousAt (fun z : ℂ => (z+v)/2) 0 by fun_prop) (by simp)
  have hA : ContinuousAt (fun z : ℂ => Complex.Gamma ((z-ν-μ)/2)) 0 := by
    have hn : -ν-μ ≠ 0 := by intro h; apply hplus; linear_combination -h
    simpa only [sub_eq_add_neg,add_assoc] using
      hG (-ν-μ) (by simp [hν,hμ]) hn
  have hB : ContinuousAt (fun z : ℂ => Complex.Gamma ((z+ν-μ)/2)) 0 := by
    simpa only [sub_eq_add_neg,add_assoc] using
      hG (ν-μ) (by simp [hν,hμ]) hminus
  have hC : ContinuousAt (fun z : ℂ => Complex.Gamma ((z-ν+μ)/2)) 0 := by
    have hn : -ν+μ ≠ 0 := by intro h; apply hminus; linear_combination -h
    simpa only [sub_eq_add_neg,add_assoc] using
      hG (-ν+μ) (by simp [hν,hμ]) hn
  have hD : ContinuousAt (fun z : ℂ => Complex.Gamma ((z+ν+μ)/2)) 0 := by
    simpa only [add_assoc] using hG (ν+μ) (by simp [hν,hμ]) hplus
  have hp : ContinuousAt (fun z : ℂ => (2 : ℂ)^(z-3)) 0 := by
    exact (continuous_id.sub continuous_const).continuousAt.const_cpow (Or.inl (by norm_num))
  have hi := Complex.differentiable_one_div_Gamma.continuous.continuousAt (x := (0 : ℂ))
  convert ((((hp.mul hA).mul hB).mul hC).mul hD).mul hi using 1
  funext z
  simp only [spectralKProductClosedValue,Pi.mul_apply,div_eq_mul_inv]

theorem schlafliBesselK_product_mellin_offDiagonal_limit (ν μ : ℂ)
    (hν : ν.re = 0) (hμ : μ.re = 0) (hplus : ν+μ ≠ 0) (hminus : ν-μ ≠ 0) :
    Tendsto (fun ε : ℝ =>
      ∫ x in Ioi (0 : ℝ), (x : ℂ)^((ε : ℂ)-1)*schlafliBesselK ν x*schlafliBesselK μ x)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hc := spectralKProductClosedValue_continuousAt_zero ν μ hν hμ hplus hminus
  have hzero : spectralKProductClosedValue ν μ 0 = 0 := by
    simp [spectralKProductClosedValue,Complex.Gamma_zero]
  have ht : Tendsto (fun ε : ℝ => spectralKProductClosedValue ν μ (ε : ℂ)) (𝓝 0) (𝓝 0) := by
    have h := hc.tendsto.comp (Complex.continuous_ofReal.continuousAt (x := (0 : ℝ))).tendsto
    change Tendsto (fun ε : ℝ => spectralKProductClosedValue ν μ (ε : ℂ))
      (𝓝 0) (𝓝 (spectralKProductClosedValue ν μ 0)) at h
    rw [hzero] at h
    exact h
  apply (ht.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  symm
  exact schlafliBesselK_product_mellin_closed ν μ (ε : ℂ) (by simpa [hν,hμ] using hε)

end ArtinMatthews
