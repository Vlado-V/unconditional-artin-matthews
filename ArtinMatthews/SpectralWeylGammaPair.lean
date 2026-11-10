module

public import ArtinMatthews.SpectralABLCoshCancellation
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
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


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory
noncomputable section

theorem spectral_weyl_gamma_pair_identity (v : ℂ) (hv : 0 < v.re) :
    spectralABLCoshCancellation (-Complex.I * (v - 1/2)) / Complex.Gamma (2*v) =
      v * (2 : ℂ)^(1-2*v) * ((Real.sqrt Real.pi : ℂ)/(Real.pi : ℂ)) *
        (Complex.Gamma (2-v) / Complex.Gamma (v+1/2)) := by
  have hv0 : v ≠ 0 := by
    intro hz
    rw [hz, Complex.zero_re] at hv
    exact (lt_irrefl 0 hv)
  have hg2 : Complex.Gamma (2*v) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by
    norm_num [Complex.mul_re]
    linarith)
  have hgh : Complex.Gamma (v+1/2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by
    norm_num [Complex.add_re, Complex.div_re]
    linarith)
  have hratio : Complex.Gamma v / Complex.Gamma (2*v) =
      (2 : ℂ)^(1-2*v) * (Real.sqrt Real.pi : ℂ) / Complex.Gamma (v+1/2) := by
    apply (div_eq_div_iff hg2 hgh).mpr
    rw [Complex.Gamma_mul_Gamma_add_half]
    ring
  have hp : (3/2 : ℂ) + Complex.I * (-Complex.I*(v-1/2)) = v+1 := by
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hm : (3/2 : ℂ) - Complex.I * (-Complex.I*(v-1/2)) = 2-v := by
    ring_nf
    simp only [Complex.I_sq]
    ring
  unfold spectralABLCoshCancellation
  rw [hp, hm, Complex.Gamma_add_one v hv0]
  calc
    _ = (v * Complex.Gamma (2-v) / (Real.pi : ℂ)) *
        (Complex.Gamma v / Complex.Gamma (2*v)) := by ring
    _ = _ := by rw [hratio]; ring

end
end ArtinMatthews
