module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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

/-! Genuine difference quotients for the weak-to-classical elliptic regularity argument. -/

noncomputable section
open Set _root_.MeasureTheory
open scoped Topology
namespace OAI.Analysis.PDE.Weak

def differenceQuotient {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (v : E) (h : ℝ) (u : E → F) (x : E) : F :=
  h⁻¹ • (u (x + h • v) - u x)

theorem differenceQuotient_add {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (v : E) (h : ℝ) (u w : E → F) (x : E) :
    differenceQuotient v h (fun y => u y + w y) x =
      differenceQuotient v h u x + differenceQuotient v h w x := by
  unfold differenceQuotient
  rw [add_sub_add_comm, smul_add]

theorem differenceQuotient_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (h : ℝ) (u w : E → ℝ) (x : E) :
    differenceQuotient v h (fun y => u y * w y) x =
      u (x + h • v) * differenceQuotient v h w x + differenceQuotient v h u x * w x := by
  simp only [differenceQuotient, smul_eq_mul]
  ring

theorem differenceQuotient_eq_integral {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (u : E → F) (hu : ContDiff ℝ 1 u) (v x : E) {h : ℝ} (hh : h ≠ 0) :
    differenceQuotient v h u x =
      ∫ t in (0 : ℝ)..1, fderiv ℝ u (x + t • (h • v)) v := by
  have hpath (t : ℝ) : HasDerivAt (fun t : ℝ => x + t • (h • v)) (h • v) t := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const (h • v)).const_add x
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => u (x + t • (h • v)))
      (h • fderiv ℝ u (x + t • (h • v)) v) t := by
    simpa only [map_smul, Function.comp_def] using!
      (hu.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t (hpath t)
  have hc : Continuous (fun t : ℝ => fderiv ℝ u (x + t • (h • v)) v) :=
    ((hu.continuous_fderiv one_ne_zero).comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) ((continuous_const.smul hc).intervalIntegrable 0 1)
  simp only [zero_smul, add_zero, one_smul, intervalIntegral.integral_smul] at hi
  unfold differenceQuotient
  rw [← hi, smul_smul, inv_mul_cancel₀ hh, one_smul]

end OAI.Analysis.PDE.Weak
