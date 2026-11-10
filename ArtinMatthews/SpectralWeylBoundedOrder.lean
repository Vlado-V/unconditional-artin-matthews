module

public import ArtinMatthews.SpectralWeylMultipliers
public import ArtinMatthews.SpectralKLKernelOrderContinuity
public import ArtinMatthews.SpectralWeylJOrderZeroLimit
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

/-! At each fixed positive modulus, the literal J/K Weyl multiplier is
bounded on the positive spectral line. The J edge uses its proved
removable limit; the K edge uses the actual cosine kernel. -/

noncomputable section
open Set Filter
open scoped Topology
namespace ArtinMatthews

theorem spectral_positive_line_bound_of_limit (F : ℝ → ℂ) (L : ℂ)
    (hL : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 L)) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hFar : ∀ r, 0 < r → ‖F r‖ ≤ C*(1+D/r)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r, 0 < r → ‖F r‖ ≤ M := by
  obtain ⟨δ,hδ,hd⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hL) 1 zero_lt_one
  let M := max (‖L‖+1) (C*(1+D/δ))
  refine ⟨M,le_trans (by positivity : 0 ≤ ‖L‖+1) (le_max_left _ _),?_⟩
  intro r hr
  by_cases hrδ : r < δ
  · have hdist := hd hr (by simpa only [Real.dist_eq,sub_zero,abs_of_pos hr] using hrδ)
    have hn : ‖F r‖ ≤ ‖F r-L‖+‖L‖ := by
      simpa only [sub_add_cancel] using norm_add_le (F r-L) L
    have hs : ‖F r‖ ≤ ‖L‖+1 := by rw [dist_eq_norm] at hdist; linarith
    exact hs.trans (le_max_left _ _)
  · have hδr : δ ≤ r := le_of_not_gt hrδ
    have hdiv := div_le_div_of_nonneg_left hD hδ hδr
    have hsum : 1+D/r ≤ 1+D/δ := by linarith
    exact (hFar r hr).trans ((mul_le_mul_of_nonneg_left hsum hC).trans (le_max_right _ _))

theorem spectralWeylJMultiplier_bounded_positive {X : ℝ} (hX : 0 < X) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r, 0 < r → ‖spectralWeylJMultiplier r X‖ ≤ M := by
  apply spectral_positive_line_bound_of_limit _ _ (spectralWeylJMultiplier_tendsto_zero_right hX)
    (C := 4*Real.pi*Real.exp (X^2/4)/X)
    (D := Real.sqrt (Real.cosh Real.pi)/Real.pi) (by positivity) (by positivity)
  intro r hr
  have h := spectralWeylJMultiplier_order_bound hr hX
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hX.le] at h
  calc
    _ ≤ (4*Real.pi*Real.exp (X^2/4)*(1+(Real.sqrt (Real.cosh Real.pi)/Real.pi)/r))/X :=
      (le_div_iff₀ hX).mpr (by simpa only [mul_comm X] using h)
    _ = _ := by ring

theorem spectralWeylKMultiplier_bounded_positive {X : ℝ} (hX : 0 < X) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r, 0 < r → ‖spectralWeylKMultiplier r X‖ ≤ M := by
  let F : ℝ → ℂ := fun r => 8*(Real.cosh (Real.pi*r) : ℂ)*(spectralKLRealKernel (2*r) X : ℂ)/(X : ℂ)
  have hEq (r : ℝ) : spectralWeylKMultiplier r X = F r := by
    rw [spectralWeylKMultiplier,ite_eq_left hX,schlafliBesselK_imaginary_eq_realKernel _ hX]
  have hF : Continuous F := by
    have hK : Continuous (fun r : ℝ => spectralKLRealKernel (2*r) X) :=
      (spectralKLRealKernel_order_continuous hX).comp (by fun_prop)
    exact ((continuous_const.mul (Complex.continuous_ofReal.comp (by fun_prop))).mul
      (Complex.continuous_ofReal.comp hK)).div_const _
  have hLim : Tendsto (fun r => spectralWeylKMultiplier r X) (𝓝[>] (0 : ℝ)) (𝓝 (F 0)) := by
    simpa only [hEq] using (hF.tendsto 0).mono_left nhdsWithin_le_nhds
  apply spectral_positive_line_bound_of_limit _ _ hLim
    (C := 4*Real.pi*Real.exp (X^2/4)/X)
    (D := Real.sqrt (Real.cosh Real.pi)/Real.pi) (by positivity) (by positivity)
  intro r hr
  have h := spectralWeylKMultiplier_order_bound hr hX
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hX.le] at h
  calc
    _ ≤ (4*Real.pi*Real.exp (X^2/4)*(1+(Real.sqrt (Real.cosh Real.pi)/Real.pi)/r))/X :=
      (le_div_iff₀ hX).mpr (by simpa only [mul_comm X] using h)
    _ = _ := by ring

end ArtinMatthews
