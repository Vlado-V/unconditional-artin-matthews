module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
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
public import Mathlib.Order.CompletePartialOrder
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
public import OAI.Analysis.PDE.Green.GreenReal


set_option backward.privateInPublic true
@[expose] public section

/-! Green's identity for actual divergence-free real second-order operators. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open _root_.MeasureTheory Measure

section Differential
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]

def realFlux (d : I → E) (K : I → I → E → ℝ) (v : E → ℝ) (i : I) (x : E) : ℝ :=
  ∑ j, K i j x * fderiv ℝ v x (d j)

theorem contDiff_realFlux (d : I → E) (K : I → I → E → ℝ) {v : E → ℝ}
    (hK : ∀ i j, ContDiff ℝ 1 (K i j)) (hv : ContDiff ℝ 2 v) (i : I) :
    ContDiff ℝ 1 (realFlux d K v i) := by
  apply ContDiff.sum
  intro j _
  exact (hK i j).mul ((hv.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const)

theorem directional_twice {v : E → ℝ} (hv : ContDiff ℝ 2 v) (a b x : E) :
    fderiv ℝ (fun y ↦ fderiv ℝ v y b) x a = fderiv ℝ (fderiv ℝ v) x a b := by
  have hD := (hv.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  rw [fderiv_clm_apply (hD x) (differentiableAt_const b)]
  simp

theorem fderiv_realFlux (d : I → E) (K : I → I → E → ℝ) {v : E → ℝ}
    (hK : ∀ i j, ContDiff ℝ 1 (K i j)) (hv : ContDiff ℝ 2 v) (i : I) (x a : E) :
    fderiv ℝ (realFlux d K v i) x a =
      ∑ j, (fderiv ℝ (K i j) x a * fderiv ℝ v x (d j) +
        K i j x * fderiv ℝ (fderiv ℝ v) x a (d j)) := by
  have hV (j : I) : ContDiff ℝ 1 (fun y ↦ fderiv ℝ v y (d j)) :=
    (hv.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  unfold realFlux
  rw [fderiv_fun_sum (fun j _ ↦ ((hK i j).mul (hV j)).differentiable (by norm_num) x)]
  simp only [_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [fderiv_fun_mul ((hK i j).differentiable (by norm_num) x)
    ((hV j).differentiable (by norm_num) x)]
  simp only [_root_.add_apply, _root_.smul_apply,
    smul_eq_mul, directional_twice hv]
  ring

theorem realFlux_divergence (d : I → E) (K : I → I → E → ℝ) {v : E → ℝ}
    (hK : ∀ i j, ContDiff ℝ 1 (K i j)) (hv : ContDiff ℝ 2 v)
    (hdiv : ∀ x j, ∑ i, fderiv ℝ (K i j) x (d i) = 0) (x : E) :
    (∑ i, fderiv ℝ (realFlux d K v i) x (d i)) =
      ∑ i, ∑ j, K i j x * fderiv ℝ (fderiv ℝ v) x (d i) (d j) := by
  simp_rw [fderiv_realFlux d K hK hv, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j ↦ fderiv ℝ (K i j) x (d i) * fderiv ℝ v x (d j))]
  simp only [← Finset.sum_mul, hdiv, zero_mul, Finset.sum_const_zero, zero_add]

end Differential

section Integral
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype I] {μ : Measure E} [IsAddHaarMeasure μ]

/-- An actual divergence-free coefficient field satisfies Green's identity
against every compactly supported `C¹` test function. -/
theorem real_operator_green (d : I → E) (K : I → I → E → ℝ)
    {u v : E → ℝ} (hK : ∀ i j, ContDiff ℝ 1 (K i j))
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 2 v) (hs : HasCompactSupport u)
    (hdiv : ∀ x j, ∑ i, fderiv ℝ (K i j) x (d i) = 0) :
    (∫ x, u x * (∑ i, ∑ j, K i j x * fderiv ℝ (fderiv ℝ v) x (d i) (d j)) ∂μ) =
      -(∫ x, ∑ i, ∑ j, K i j x * fderiv ℝ u x (d i) * fderiv ℝ v x (d j) ∂μ) := by
  have h := integral_divergence_by_parts (μ := μ) hu hs d (realFlux d K v)
    (contDiff_realFlux d K hK hv)
  simp_rw [realFlux_divergence d K hK hv hdiv] at h
  convert h using 3
  simp only [realFlux, Finset.mul_sum]
  funext x
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end Integral
end OAI.Analysis.PDE.Green
