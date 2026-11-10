module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
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
public import OAI.NumberTheory.TwoPoint.Halasz.HalaszCubicLaplace


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-! Cubic logarithmic cancellation absorbs a strip displacement. -/
namespace TwoPointCorrelations

lemma halasz_cubic_maximum {δ y L : ℝ} (hδ : 0≤δ) (hy : 0≤y) (hL : 0<L) :
    δ*y-y^3/((10^15:ℝ)*L^2)≤(10^9:ℝ)*δ^(3/2:ℝ)*L := by
  have hh := halasz_cubic_balance hδ hy (show 0<(10^6:ℝ)*L by positivity)
  have he : (1000:ℝ)*((10^6:ℝ)*L)^2=(10^15:ℝ)*L^2 := by ring
  rw [he] at hh
  have hn : 0≤y^3/(2000*((10^6:ℝ)*L)^2) := by positivity
  nlinarith

lemma halasz_log_cubic_identity {N L lam : ℝ} (hL : 0<L)
    (hy : 0<Real.log N) (hLlam : L=lam*Real.log N) :
    (-1/((10^15:ℝ)*lam^2))*Real.log N =
      -(Real.log N)^3/((10^15:ℝ)*L^2) := by
  have hlam : 0<lam := by nlinarith
  rw [hLlam]
  field_simp

end TwoPointCorrelations

end OAI
