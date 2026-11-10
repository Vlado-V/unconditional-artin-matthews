module

public import ArtinMatthews.SpectralBesselI
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


set_option backward.privateInPublic true
@[expose] public section

/-! Continuity of the actual I series away from its power branch point. -/

noncomputable section

namespace ArtinMatthews

theorem spectralBesselI_continuousAt (ν : ℂ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (spectralBesselI ν) x := by
  unfold spectralBesselI
  apply ContinuousAt.mul
  · apply ContinuousAt.cpow (by fun_prop) continuousAt_const
    have hp : 0 < x/2 := half_pos hx
    simpa only [Complex.ofReal_div,Complex.ofReal_ofNat] using
      (Complex.ofReal_mem_slitPlane.mpr hp)
  · exact (Complex.analyticAt_regularizedHGFun_zero (b := {ν+1}) _).continuousAt.comp (by fun_prop)

end ArtinMatthews
