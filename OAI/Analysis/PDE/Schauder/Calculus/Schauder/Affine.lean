module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.Normed.Function.Holder.Banach.Construct
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Perturbation
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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
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
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.PotentialDerivatives


set_option backward.privateInPublic true
@[expose] public section

/-! Affine changes of variables for genuine derivatives and Hölder data. -/

noncomputable section
open Set Metric
open scoped Topology BoundedContinuousFunction
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

theorem second_fderiv_comp_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : E → ℝ) (hu : ContDiff ℝ 2 u) (L : E →L[ℝ] E) (x₀ x v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => u (x₀ + L y))) x v w =
      fderiv ℝ (fderiv ℝ u) (x₀ + L x) (L v) (L w) := by
  let φ := fun y => x₀ + L y
  have hφ (y) : HasFDerivAt φ L y := by
    simpa only [zero_add] using (L.hasFDerivAt (x := y)).const_add x₀
  have hφc : ContDiff ℝ 2 φ := contDiff_const.add L.contDiff
  have hD : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hDcomp : ContDiff ℝ 1 (fderiv ℝ (u ∘ φ)) := (hu.comp hφc).fderiv_right (by norm_num)
  have he : (fun y => fderiv ℝ (u ∘ φ) y w) = fun y => fderiv ℝ u (φ y) (L w) := by
    funext y
    rw [fderiv_comp y (hu.differentiable (by norm_num) _) (hφ y).differentiableAt, (hφ y).fderiv]
    rfl
  change fderiv ℝ (fderiv ℝ (u ∘ φ)) x v w = _
  rw [← fderiv_apply_const _ x w v (hDcomp.differentiable one_ne_zero x), he]
  have hfun : (fun y => fderiv ℝ u (φ y) (L w)) = (fun y => fderiv ℝ u y (L w)) ∘ φ := rfl
  rw [hfun, fderiv_comp x ((hD.clm_apply contDiff_const).differentiable one_ne_zero _)
    (hφ x).differentiableAt, (hφ x).fderiv, ContinuousLinearMap.comp_apply,
    fderiv_apply_const _ (φ x) (L w) (L v) (hD.differentiable one_ne_zero _)]

theorem nondivergence_dilate {m : ℕ}
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (hu : ContDiff ℝ 2 u)
    (x₀ x : EuclideanSpace ℝ (Fin m)) (r : ℝ) :
    nondivergenceOperator (fun y => A (x₀ + r • y)) (fun y => u (x₀ + r • y)) x =
      r ^ 2 * nondivergenceOperator A u (x₀ + r • x) := by
  have hD (v w : EuclideanSpace ℝ (Fin m)) :=
    second_fderiv_comp_affine u hu (r • ContinuousLinearMap.id ℝ _) x₀ x v w
  simp only [smul_apply, ContinuousLinearMap.id_apply] at hD
  unfold nondivergenceOperator
  simp_rw [hD]
  simp only [map_smul, smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

def holderAffinePullback {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {α : ℝ}
    (hα : 0 ≤ α) (f : OAI.Analysis.Normed.Function.Holder.HolderMap E F α) (x₀ : E) (r : ℝ) : OAI.Analysis.Normed.Function.Holder.HolderMap E F α := by
  let φ : C(E, E) := ⟨fun x => x₀ + r • x, continuous_const.add (continuous_const.smul continuous_id)⟩
  let b : E →ᵇ F := (OAI.Analysis.Normed.Function.Holder.HolderMap.value f).compContinuous φ
  refine OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα b (C := ‖f‖ * |r| ^ α) ?_
  intro x y
  change ‖OAI.Analysis.Normed.Function.Holder.HolderMap.value f (x₀ + r • x) - OAI.Analysis.Normed.Function.Holder.HolderMap.value f (x₀ + r • y)‖ ≤ _
  have he : x₀ + r • x - (x₀ + r • y) = r • (x - y) := by rw [smul_sub]; abel
  have h := OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le f (x₀ + r • x) (x₀ + r • y)
  rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg _) (norm_nonneg _)] at h
  rw [dist_eq_norm]
  exact h.trans_eq (by ring)

@[simp] theorem holderAffinePullback_value {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ} (hα : 0 ≤ α) (f : OAI.Analysis.Normed.Function.Holder.HolderMap E F α) (x₀ : E) (r : ℝ) (x : E) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (holderAffinePullback hα f x₀ r) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value f (x₀ + r • x) := rfl

end OAI.Analysis.PDE.Schauder
