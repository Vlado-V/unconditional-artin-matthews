module

public import ArtinMatthews.SpectralHyperbolicComplexGreen
public import ArtinMatthews.SpectralGamma0EisensteinPDE
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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


set_option backward.privateInPublic true
@[expose] public section

/-! Finite linearity of the actual second-order plane operator. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace ArtinMatthews

theorem spectralPlane_hessian_finset_sum {ι : Type*} (T : Finset ι)
    (F : ι → ℝ×ℝ → ℂ)
    (hF : ∀ i ∈ T, ContDiffOn ℝ 2 (F i) {p : ℝ×ℝ | 0 < p.2})
    (p : ℝ×ℝ) (hp : 0 < p.2) :
    fderiv ℝ (fderiv ℝ (fun q => ∑ i ∈ T, F i q)) p=
      ∑ i ∈ T, fderiv ℝ (fderiv ℝ (F i)) p := by
  have hd (i) (hi : i ∈ T) (q : ℝ×ℝ) (hq : 0 < q.2) :
      DifferentiableAt ℝ (F i) q :=
    ((hF i hi).contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hq)).differentiableAt
      (by norm_num)
  have hdd (i) (hi : i ∈ T) : DifferentiableAt ℝ (fderiv ℝ (F i)) p :=
    (((hF i hi).contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hp)).fderiv_right
      (by norm_num : (1:ℕ∞ω)+1 ≤ 2)).differentiableAt (by norm_num)
  have he : fderiv ℝ (fun q => ∑ i ∈ T, F i q) =ᶠ[𝓝 p]
      fun q => ∑ i ∈ T, fderiv ℝ (F i) q := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hp] with q hq
    exact fderiv_fun_sum (fun i hi => hd i hi q hq)
  rw [he.fderiv_eq]
  exact fderiv_fun_sum hdd

theorem spectralPlanePositiveHyperbolic_finset_sum {ι : Type*} (T : Finset ι)
    (F : ι → ℝ×ℝ → ℂ)
    (hF : ∀ i ∈ T, ContDiffOn ℝ 2 (F i) {p : ℝ×ℝ | 0 < p.2})
    (p : ℝ×ℝ) (hp : 0 < p.2) :
    spectralPlanePositiveHyperbolic (fun q => ∑ i ∈ T, F i q) p=
      ∑ i ∈ T, spectralPlanePositiveHyperbolic (F i) p := by
  have hc := (ContDiffOn.sum hF).contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hp)
  have hd := (hc.fderiv_right (by norm_num : (1:ℕ∞ω)+1≤2)).differentiableAt (by norm_num)
  rw [spectralPlanePositiveHyperbolic_eq_hessian _ p hd,
    spectralPlane_hessian_finset_sum T F hF p hp,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hc' := (hF i hi).contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hp)
  exact (spectralPlanePositiveHyperbolic_eq_hessian _ p
    ((hc'.fderiv_right (by norm_num : (1:ℕ∞ω)+1≤2)).differentiableAt (by norm_num))).symm

theorem spectralPlanePositiveHyperbolic_smul (c : ℂ) (F : ℝ×ℝ → ℂ)
    (hF : ContDiffOn ℝ 2 F {p : ℝ×ℝ | 0 < p.2}) (p : ℝ×ℝ) (hp : 0 < p.2) :
    spectralPlanePositiveHyperbolic (c • F) p=c*spectralPlanePositiveHyperbolic F p := by
  have hc := hF.contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hp)
  have hd := (hc.fderiv_right (by norm_num : (1:ℕ∞ω)+1≤2)).differentiableAt (by norm_num)
  have hfc : ContDiffOn ℝ 2 (c • F) {p : ℝ×ℝ | 0 < p.2} :=
    (contDiffOn_const : ContDiffOn ℝ 2 (fun _ : ℝ×ℝ => c) {p | 0 < p.2}).mul hF
  have hc' := hfc.contDiffAt
    ((isOpen_lt continuous_const continuous_snd).mem_nhds hp)
  have hd' := (hc'.fderiv_right (by norm_num : (1:ℕ∞ω)+1≤2)).differentiableAt (by norm_num)
  rw [spectralPlanePositiveHyperbolic_eq_hessian _ p hd',
    spectralPlanePositiveHyperbolic_eq_hessian _ p hd,fderiv_const_smul_field]
  have he := congrFun (fderiv_const_smul_field (𝕜 := ℝ) (R := ℂ) (f := fderiv ℝ F) c) p
  rw [he]
  change -((p.2:ℂ)^2)*spectralPlaneHessianTrace (c • fderiv ℝ (fderiv ℝ F) p)=_
  rw [spectralPlaneHessianTrace_smul]
  ring

end ArtinMatthews
