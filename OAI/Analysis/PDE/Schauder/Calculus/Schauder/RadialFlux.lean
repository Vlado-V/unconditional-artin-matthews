module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact one-dimensional flux integral for a smooth radial power. -/

noncomputable section
open _root_.MeasureTheory Set
namespace OAI.Analysis.PDE.Schauder

def radialFlux (m : ℕ) (p s t : ℝ) : ℝ :=
  2 * p * t ^ m * (s + t ^ 2) ^ (p - 1)

def radialTrace (m : ℕ) (p s t : ℝ) : ℝ :=
  2 * p * (m : ℝ) * (s + t ^ 2) ^ (p - 1) +
    4 * p * (p - 1) * (s + t ^ 2) ^ (p - 2) * t ^ 2

theorem hasDerivAt_radialFlux {m : ℕ} (hm : 1 ≤ m) (p : ℝ) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    HasDerivAt (radialFlux m p s) (t ^ (m - 1) * radialTrace m p s t) t := by
  have hb := (((hasDerivAt_id t).pow 2).const_add s).rpow_const
    (p := p - 1) (Or.inl (ne_of_gt (add_pos_of_pos_of_nonneg hs (sq_nonneg t))))
  have h := (((hasDerivAt_id t).pow m).mul hb).const_mul (2 * p)
  convert h using 1
  · funext q
    dsimp [radialFlux]
    ring
  · have ht : t ^ m = t ^ (m - 1) * t := by
      rw [← pow_succ, Nat.sub_add_cancel hm]
    dsimp [radialTrace]
    rw [ht, show p - 1 - 1 = p - 2 by ring]
    ring

theorem continuous_radialTrace (m : ℕ) (p : ℝ) {s : ℝ} (hs : 0 < s) :
    Continuous (radialTrace m p s) := by
  have hb : Continuous (fun t : ℝ => s + t ^ 2) := by fun_prop
  have hn (t : ℝ) : s + t ^ 2 ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hs (sq_nonneg t))
  have h1 : Continuous (fun t : ℝ => (s + t ^ 2) ^ (p - 1)) := hb.rpow_const (fun t => Or.inl (hn t))
  have h2 : Continuous (fun t : ℝ => (s + t ^ 2) ^ (p - 2)) := hb.rpow_const (fun t => Or.inl (hn t))
  exact ((continuous_const.mul h1).add ((continuous_const.mul h2).mul (continuous_id.pow 2)))

theorem integral_radialTrace {m : ℕ} (hm : 1 ≤ m) (p : ℝ) {s R : ℝ} (hs : 0 < s) (hR : 0 ≤ R) :
    (∫ t in Ioo (0 : ℝ) R, t ^ (m - 1) * radialTrace m p s t) =
      2 * p * R ^ m * (s + R ^ 2) ^ (p - 1) := by
  have hi : IntervalIntegrable (fun t : ℝ => t ^ (m - 1) * radialTrace m p s t) volume 0 R :=
    ((continuous_id.pow _).mul (continuous_radialTrace m p hs)).intervalIntegrable _ _
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_radialFlux hm p hs t) hi
  rw [intervalIntegral.integral_of_le hR, integral_Ioc_eq_integral_Ioo] at he
  simpa [radialFlux, show m ≠ 0 by omega] using he

end OAI.Analysis.PDE.Schauder
