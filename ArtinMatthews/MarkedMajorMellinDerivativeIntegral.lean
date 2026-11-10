module

public import ArtinMatthews.MarkedMajorMellinKernel
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import ArtinMatthews.MarkedMajorMellinDerivative
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory
open scoped ContDiff
noncomputable section

theorem markedMajorMellinKernel_derivative_eq_zero (ρ ρ' ψ : SchwartzMap ℝ ℂ)
    {a b R X : ℝ} (ha : 0 < a) (hX : 0 < X)
    (hρ : tsupport ρ ⊆ Icc a b) (hρ' : tsupport ρ' ⊆ Icc a b)
    (hψ : tsupport ψ ⊆ Icc (-R) R) (theta : ℝ) (n : ℕ) (p : ℝ × ℝ)
    (hp : p ∉ markedMajorMellinSupportBox a b R) :
    iteratedFDeriv ℝ n (markedMajorMellinKernelFun ρ ρ' ψ X theta) p = 0 := by
  by_contra hn
  exact hp (markedMajorMellinKernel_tsupport ρ ρ' ψ ha hX hρ hρ' hψ theta
    (support_iteratedFDeriv_subset n hn))

theorem markedMajorMellinKernel_derivative_integrable (ρ ρ' ψ : SchwartzMap ℝ ℂ)
    {a b R X : ℝ} (ha : 0 < a) (hX : 0 < X)
    (hρ : tsupport ρ ⊆ Icc a b) (hρ' : tsupport ρ' ⊆ Icc a b)
    (hψ : tsupport ψ ⊆ Icc (-R) R) (theta : ℝ) (n : ℕ) :
    Integrable (iteratedFDeriv ℝ n (markedMajorMellinKernelFun ρ ρ' ψ X theta)) :=
  ((markedMajorMellinKernel_contDiff ρ ρ' ψ X theta).continuous_iteratedFDeriv (by simp)).integrable_of_hasCompactSupport
    ((markedMajorMellinKernel_hasCompactSupport ρ ρ' ψ ha hX hρ hρ' hψ theta).iteratedFDeriv n)

/-- Actual L1 derivative bounds, with constants independent of the moving scale. -/
theorem markedMajorMellinKernel_derivative_L1_bound (ρ ρ' ψ : SchwartzMap ℝ ℂ)
    {a b R : ℝ} (ha : 0 < a)
    (hρ : tsupport ρ ⊆ Icc a b) (hρ' : tsupport ρ' ⊆ Icc a b)
    (hψ : tsupport ψ ⊆ Icc (-R) R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ X ≥ 1, ∀ theta : ℝ,
      (∫ p : ℝ × ℝ, ‖iteratedFDeriv ℝ n (markedMajorMellinKernelFun ρ ρ' ψ X theta) p‖) ≤
        C*(1+|theta|)^n := by
  obtain ⟨C,hC,hbound⟩ := markedMajorMellinKernel_compact_derivative_bound ρ ρ' ψ a b R n
  let K := markedMajorMellinSupportBox a b R
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  refine ⟨C*(volume.real K+1),by positivity,fun X hX theta => ?_⟩
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have heq : (∫ p in K, ‖iteratedFDeriv ℝ n (markedMajorMellinKernelFun ρ ρ' ψ X theta) p‖) =
      ∫ p, ‖iteratedFDeriv ℝ n (markedMajorMellinKernelFun ρ ρ' ψ X theta) p‖ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by
      rw [markedMajorMellinKernel_derivative_eq_zero ρ ρ' ψ ha hXpos hρ hρ' hψ theta n p hp,norm_zero])
  have H := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := K)
    (f := fun p : ℝ × ℝ => ‖iteratedFDeriv ℝ n (markedMajorMellinKernelFun ρ ρ' ψ X theta) p‖)
    hK.measure_lt_top (fun p hp => by
      simpa only [norm_norm] using hbound X hX theta p hp)
  rw [heq,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] at H
  calc
    _ ≤ (C*(1+|theta|)^n)*volume.real K := H
    _ ≤ (C*(volume.real K+1))*(1+|theta|)^n := by nlinarith [pow_nonneg (by positivity : 0 ≤ 1+|theta|) n]

end
end ArtinMatthews
