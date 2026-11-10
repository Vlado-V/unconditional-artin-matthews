module

public import ArtinMatthews.MarkedMajorMellinKernel
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import ArtinMatthews.MarkedMajorMellinDerivativeIntegral
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
open scoped ContDiff BigOperators
noncomputable section

/-- One constant controls every derivative up to n, with its own sharp phase degree. -/
theorem markedMajorMellinKernel_uniform_L1_bounds (ρ ρ' ψ : SchwartzMap ℝ ℂ)
    {a b R : ℝ} (ha : 0 < a)
    (hρ : tsupport ρ ⊆ Icc a b) (hρ' : tsupport ρ' ⊆ Icc a b)
    (hψ : tsupport ψ ⊆ Icc (-R) R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k ≤ n, ∀ X ≥ 1, ∀ theta : ℝ,
      (∫ p : ℝ × ℝ, ‖iteratedFDeriv ℝ k (markedMajorMellinKernelFun ρ ρ' ψ X theta) p‖) ≤
        C*(1+|theta|)^k := by
  classical
  choose C hC hb using (fun k : ℕ =>
    markedMajorMellinKernel_derivative_L1_bound ρ ρ' ψ ha hρ hρ' hψ k)
  let D : ℝ := 1 + ∑ k ∈ Finset.range (n+1), C k
  have hsum : 0 ≤ ∑ k ∈ Finset.range (n+1), C k :=
    Finset.sum_nonneg (fun k _ => (hC k).le)
  refine ⟨D,by dsimp [D]; linarith,fun k hk X hX theta => ?_⟩
  have hle : C k ≤ ∑ i ∈ Finset.range (n+1), C i :=
    Finset.single_le_sum (fun i _ => (hC i).le) (Finset.mem_range.mpr (by omega))
  exact (hb k X hX theta).trans (mul_le_mul_of_nonneg_right
    (by dsimp [D]; linarith) (by positivity))

end
end ArtinMatthews
