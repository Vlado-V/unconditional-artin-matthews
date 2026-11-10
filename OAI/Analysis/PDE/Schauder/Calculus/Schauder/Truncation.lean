module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Cutoff
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.KernelScale
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Reflection


set_option backward.privateInPublic true
@[expose] public section

/-! Globally smooth, even far-field Newtonian kernels and their odd derivatives. -/

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped Topology RealInnerProductSpace
namespace OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem newtonianEntry_neg (m : ℕ) (v w y : E) : newtonianEntry m v w (-y) = newtonianEntry m v w y := by
  by_cases hy : y = 0
  · simp [hy]
  · rw [newtonianEntry_formula m v w (neg_ne_zero.mpr hy), newtonianEntry_formula m v w hy]
    simp

def truncatedNewtonianEntry (m : ℕ) (v w : E) (r : ℝ) (y : E) : ℝ :=
  (1 - radialCutoff r y) * newtonianEntry m v w y

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem truncatedNewtonianEntry_zero (m : ℕ) (v w : E) {r : ℝ} (hr : 0 < r)
    {y : E} (hy : ‖y‖ ≤ r) : truncatedNewtonianEntry m v w r y = 0 := by
  simp [truncatedNewtonianEntry, radialCutoff_one hr hy]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem truncatedNewtonianEntry_eventually_zero (m : ℕ) (v w : E) {r : ℝ} (hr : 0 < r)
    {y : E} (hy : ‖y‖ < r) : truncatedNewtonianEntry m v w r =ᶠ[𝓝 y] fun _ => 0 := by
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hy] with z hz
  exact truncatedNewtonianEntry_zero m v w hr hz.le

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem contDiff_truncatedNewtonianEntry (m : ℕ) (v w : E) {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (truncatedNewtonianEntry m v w r) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y = 0
  · subst y
    exact contDiffAt_const.congr_of_eventuallyEq
      (truncatedNewtonianEntry_eventually_zero m v w hr (by simpa using hr))
  · exact (contDiffAt_const.sub (contDiff_radialCutoff r).contDiffAt).mul
      ((contDiffAt_newtonianEntry m v w hy).of_le le_top)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem truncatedNewtonianEntry_neg (m : ℕ) (v w y : E) (r : ℝ) :
    truncatedNewtonianEntry m v w r (-y) = truncatedNewtonianEntry m v w r y := by
  simp only [truncatedNewtonianEntry, radialCutoff_neg, newtonianEntry_neg]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem truncatedNewtonianEntry_fderiv_neg (m : ℕ) (v w y : E) {r : ℝ} (hr : 0 < r) :
    fderiv ℝ (truncatedNewtonianEntry m v w r) (-y) =
      -fderiv ℝ (truncatedNewtonianEntry m v w r) y := by
  have hdiff := (contDiff_truncatedNewtonianEntry m v w hr).differentiable (by simp)
  have h := fderiv_reflect_translate (truncatedNewtonianEntry m v w r) hdiff 0 y
  have he : (fun z : E => truncatedNewtonianEntry m v w r (0 - z)) = truncatedNewtonianEntry m v w r := by
    funext z
    simp only [zero_sub, truncatedNewtonianEntry_neg]
  rw [he, zero_sub] at h
  exact (neg_eq_iff_eq_neg.mpr h).symm

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem truncatedNewtonianEntry_fderiv_zero (m : ℕ) (v w : E) {r : ℝ} (hr : 0 < r)
    {y : E} (hy : ‖y‖ < r) : fderiv ℝ (truncatedNewtonianEntry m v w r) y = 0 := by
  rw [(truncatedNewtonianEntry_eventually_zero m v w hr hy).fderiv_eq]
  simp

theorem truncatedNewtonianEntry_fderiv_integral_zero (m : ℕ) (v w u : E) {r : ℝ} (hr : 0 < r)
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    (∫ y, fderiv ℝ (truncatedNewtonianEntry m v w r) y u ∂μ) = 0 := by
  have h := integral_neg_eq_self (fun y : E => fderiv ℝ (truncatedNewtonianEntry m v w r) y u) μ
  simp only [truncatedNewtonianEntry_fderiv_neg m v w _ hr, neg_apply, integral_neg] at h
  linarith

end OAI.Analysis.PDE.Schauder
