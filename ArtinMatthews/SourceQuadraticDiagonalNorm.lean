module

public import ArtinMatthews.SourceQuadraticBlockPoissonExpansion
public import ArtinMatthews.SourceReflectionExteriorRows
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The compact original bump bounds the literal principal block uniformly
in its common-ideal mask. -/

namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain VaryingKummerAnalytic
open scoped NumberField Classical BigOperators

noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "χ" => sourceReflectionQuadraticSymbol F S₀ hζ

omit [IsTotallyComplex F] in
theorem sourceQuadraticBlockRowKernel_norm_le_card (rows : Finset E)
    (w : E → ℝ) (hw₀ : ∀ d ∈ rows, 0 ≤ w d) (hw₁ : ∀ d ∈ rows, w d ≤ 1)
    (g e : E) :
    ‖sourceQuadraticBlockRowKernel F S₀ hζ rows w g e‖ ≤ rows.card := by
  unfold sourceQuadraticBlockRowKernel
  calc
    _ ≤ ∑ d ∈ rows, ‖if Disjoint d.support g.support then (w d : ℂ) * χ d e else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _d ∈ rows, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      split_ifs
      · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw₀ d hd)]
        exact (mul_le_mul_of_nonneg_left
          (sourceReflectionQuadraticSymbol_norm_le_one F S₀ hζ d e) (hw₀ d hd)).trans
          (by simpa only [mul_one] using hw₁ d hd)
      · simp only [norm_zero, zero_le_one]
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]

theorem sourceQuadraticBlockIdealFull_zero_eq_finite {M : ℝ} (hM : 0 < M) (g : E) :
    sourceQuadraticBlockIdealFull F S₀ hζ M g 0 =
      sourceQuadraticBlockRowKernel F S₀ hζ
        (sourceReflectionBoundedExponents F S₀ (5 * M / 2))
        (sourceQuadraticB2RowWeight F S₀ M) g 0 := by
  have he : sourceReflectionIsSquarefree (0 : E) := by
    intro P
    simp only [Finsupp.zero_apply, zero_le_one]
  have h := sourceQuadraticBlock_character_tsum F S₀ hζ M g 0 he (fun _ => True)
  simp only [and_true] at h
  unfold sourceQuadraticBlockIdealFull
  rw [← h]
  rw [tsum_eq_sum (s := sourceReflectionBoundedExponents F S₀ (5 * M / 2)) (fun d hd => ?_)]
  · rfl
  · have hw : sourceQuadraticB2RowWeight F S₀ M d = 0 := by
      by_contra hn
      exact hd ((sourceReflection_mem_boundedExponents F S₀ (by positivity) d).mpr
        (sourceQuadraticB2RowWeight_support F S₀ hM d hn).2)
    simp only [hw, Complex.ofReal_zero, zero_mul, ite_self]

theorem sourceQuadraticDiagonalNorm_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 1 ≤ M → ∀ g : E,
      ‖sourceQuadraticBlockIdealFull F S₀ hζ M g 0‖ ≤ C * M ∧
      ∀ K : ℝ, ‖sourceQuadraticBlockRowKernel F S₀ hζ
        (sourceQuadraticB2Rows F S₀ M K) (sourceQuadraticB2RowWeight F S₀ M) g 0‖ ≤ C * M := by
  obtain ⟨C, hC, hcount⟩ := exists_sourceReflectionExteriorCard_le F S₀
  refine ⟨C * (5 / 2), by positivity, ?_⟩
  intro M hM g
  have hM₀ : 0 < M := zero_lt_one.trans_le hM
  have hbound (rows : Finset E) (hr : ∀ d ∈ rows, (q d : ℝ) ≤ 5 * M / 2) :
      ‖sourceQuadraticBlockRowKernel F S₀ hζ rows (sourceQuadraticB2RowWeight F S₀ M) g 0‖ ≤
        C * (5 / 2) * M := by
    calc
      _ ≤ (rows.card : ℝ) := sourceQuadraticBlockRowKernel_norm_le_card F S₀ hζ rows _
        (fun d _ => sourceQuadraticB2Bump_nonneg _) (fun d _ => sourceQuadraticB2Bump_le_one _) g 0
      _ ≤ C * (5 * M / 2) := hcount _ (by linarith) rows hr
      _ = _ := by ring
  constructor
  · rw [sourceQuadraticBlockIdealFull_zero_eq_finite F S₀ hζ hM₀ g]
    exact hbound _ (fun d hd => (sourceReflection_mem_boundedExponents F S₀ (by positivity) d).mp hd)
  · intro K
    exact hbound _ (fun d hd => ((sourceQuadratic_mem_B2Rows F S₀ hM₀.le d).mp hd).1)

theorem sourceQuadraticBlockPrincipalPoissonSum_norm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 1 ≤ M → ∀ g : E,
      ‖sourceQuadraticBlockPrincipalPoissonSum F S₀ hζ M g‖ ≤ C * M := by
  obtain ⟨C, hC, hbound⟩ := sourceQuadraticDiagonalNorm_bounds F S₀ hζ
  refine ⟨C, hC, ?_⟩
  intro M hM g
  rw [← sourceQuadraticBlockIdealFull_eq_principalPoisson F S₀ hζ (zero_lt_one.trans_le hM) g]
  exact (hbound M hM g).1

end
end ArtinMatthews.SourceEulerAssembly
