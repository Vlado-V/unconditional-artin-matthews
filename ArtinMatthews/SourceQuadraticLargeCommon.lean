module

public import ArtinMatthews.SourceQuadraticCommonIdeal
public import ArtinMatthews.SourceQuadraticShortColumns
public import ArtinMatthews.SourceQuadraticGcdStrip
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import OAI.NumberTheory.DirichletL.CubicSieve.CrossFactorization


set_option backward.privateInPublic true
@[expose] public section

/-! The large-common-ideal term costs two squarefree-divisor counts:
one for the common ideal and one for the coprimality expansion. -/

namespace ArtinMatthews.SourceEulerAssembly
noncomputable section
open NumberField IsDedekindDomain
open OAI.FiniteSieveOperator
open scoped NumberField Classical BigOperators

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

local notation "E" => SourcePrimeExponents F S₀
local notation "P" => SourceExteriorPrime F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "χ" => sourceReflectionQuadraticSymbol F S₀ hζ

theorem sourceQuadraticB3Block_norm_le_short (rows cols : Finset E) (w : E → ℝ)
    (hw : ∀ d ∈ rows, 0 ≤ w d) (a : E → ℂ) (g : E)
    {N G C : ℝ} (hN : 0 ≤ N) (hG : 0 < G) (hg : G ≤ (q g : ℝ))
    (hcols : ∀ b ∈ cols, (q b : ℝ) ≤ N ∧ sourceReflectionIsSquarefree b)
    (hdiv : ∀ b ∈ cols, ((sourceQuadraticSquarefreeDivisors F S₀ b).card : ℝ) ≤ C) :
    ‖sourceQuadraticB3Block F S₀ hζ rows cols w a g‖ ≤
      sourceQuadraticB2Norm F S₀ hζ rows w (N / G) *
        (C * QuadraticScale.coeffMass (sourceQuadraticDivisibleColumns F S₀ cols g) a) := by
  let D := sourceQuadraticDivisibleColumns F S₀ cols g
  let A := sourceQuadraticShortMatrix F S₀ hζ rows cols w g
  let S (b : D) := (b.val - g).support
  let U : Finset P := D.biUnion (fun b => (b - g).support)
  let mask (d : rows) : ℂ := ((‖χ d.val g‖ ^ 2 : ℝ) : ℂ)
  have hS (b : D) : S b ⊆ U := fun p hp => Finset.mem_biUnion.mpr ⟨b.val, b.property, hp⟩
  have hmask (d : rows) : ‖mask d‖ ≤ 1 := by
    change ‖((‖χ d.val g‖ ^ 2 : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_one₀ (norm_nonneg _) (sourceReflectionQuadraticSymbol_norm_le_one F S₀ hζ _ _)
  have hB := OAI.CoprimeSieveOperator.coprime_gram_operator_bound
    U S hS A (fun b => a b.val) mask 1 (by norm_num) hmask
  have hmass : (∑ b : D, (2 : ℝ) ^ (S b).card * ‖a b.val‖ ^ 2) ≤
      C * QuadraticScale.coeffMass D a := by
    rw [QuadraticScale.coeffMass, Finset.mul_sum]
    rw [← Finset.sum_coe_sort D (fun b => C * ‖a b‖ ^ 2)]
    apply Finset.sum_le_sum
    intro b _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hb := ((sourceQuadratic_mem_divisibleColumns F S₀ cols g b.val).mp b.property).1
    calc
      (2 : ℝ) ^ (S b).card ≤ (2 : ℝ) ^ b.val.support.card :=
        pow_le_pow_right₀ (by norm_num) (Finset.card_le_card Finsupp.support_tsub)
      _ = ((sourceQuadraticSquarefreeDivisors F S₀ b.val).card : ℝ) := by
        rw [sourceQuadraticSquarefreeDivisors_card, Nat.cast_pow]
        norm_num
      _ ≤ C := hdiv b.val hb
  have hnonneg : 0 ≤ (∑ b : D, (2 : ℝ) ^ (S b).card * ‖a b.val‖ ^ 2) := by positivity
  calc
    _ ≤ ‖operator A‖ ^ 2 * ∑ b : D, (2 : ℝ) ^ (S b).card * ‖a b.val‖ ^ 2 := by
      rw [sourceQuadraticB3Block_eq_coprime_gram F S₀ hζ rows cols w hw a g]
      simpa only [one_mul] using hB
    _ ≤ _ := mul_le_mul
      (sourceQuadraticShortMatrix_norm_le F S₀ hζ rows cols w g hN hG hg hcols) hmass
      hnonneg (sourceQuadraticB2Norm_nonneg F S₀ hζ rows w (N / G))

theorem sourceQuadratic_divisible_mass_sum_le (cols G : Finset E) (a : E → ℂ)
    (hG : ∀ g ∈ G, sourceReflectionIsSquarefree g) {C : ℝ}
    (hdiv : ∀ b ∈ cols, ((sourceQuadraticSquarefreeDivisors F S₀ b).card : ℝ) ≤ C) :
    (∑ g ∈ G, QuadraticScale.coeffMass (sourceQuadraticDivisibleColumns F S₀ cols g) a) ≤
      C * QuadraticScale.coeffMass cols a := by
  unfold QuadraticScale.coeffMass
  simp only [sourceQuadraticDivisibleColumns, Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro b hb
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hsub : G.filter (fun g => g ≤ b) ⊆ sourceQuadraticSquarefreeDivisors F S₀ b := by
    intro g hg
    obtain ⟨hGg, hgb⟩ := Finset.mem_filter.mp hg
    exact (sourceQuadratic_mem_squarefreeDivisors F S₀ b g).mpr ⟨hgb, hG g hGg⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hdiv b hb)

theorem sourceQuadratic_common_squarefree (cols : Finset E)
    (hcols : ∀ b ∈ cols, sourceReflectionIsSquarefree b) (g : E)
    (hg : g ∈ sourceQuadraticCommonIdeals F S₀ cols) : sourceReflectionIsSquarefree g := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hg
  have hp₁ := (Finset.mem_product.mp hp).1
  have hle : p.1 ⊓ p.2 ≤ p.1 := inf_le_left
  intro Q
  exact (hle Q).trans (hcols p.1 hp₁ Q)

theorem sourceQuadratic_largeCommon_norm_sum (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N G : ℝ}, 1 ≤ N → 0 < G → ∀ (rows cols : Finset E)
      (w : E → ℝ), (∀ d ∈ rows, 0 ≤ w d) →
      (∀ b ∈ cols, (q b : ℝ) ≤ N ∧ sourceReflectionIsSquarefree b) → ∀ a : E → ℂ,
      (∑ g ∈ (sourceQuadraticCommonIdeals F S₀ cols).filter (fun g => G < (q g : ℝ)),
        ‖sourceQuadraticB3Block F S₀ hζ rows cols w a g‖) ≤
        C * N^ε * sourceQuadraticB2Norm F S₀ hζ rows w (N / G) * QuadraticScale.coeffMass cols a := by
  obtain ⟨c, hc, hcdiv⟩ := sourceQuadraticSquarefreeDivisors_small_power F S₀ (ε / 2) (half_pos hε)
  refine ⟨c^2, sq_pos_of_pos hc, ?_⟩
  intro N G hN hG rows cols w hw hcols a
  let D := (sourceQuadraticCommonIdeals F S₀ cols).filter (fun g => G < (q g : ℝ))
  let B := sourceQuadraticB2Norm F S₀ hζ rows w (N / G)
  let R := c * N^(ε / 2)
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hB : 0 ≤ B := sourceQuadraticB2Norm_nonneg F S₀ hζ rows w (N / G)
  have hdiv (b : E) (hb : b ∈ cols) : ((sourceQuadraticSquarefreeDivisors F S₀ b).card : ℝ) ≤ R :=
    (hcdiv b).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (hcols b hb).1 (half_pos hε).le) hc.le)
  have hsf (g : E) (hg : g ∈ D) : sourceReflectionIsSquarefree g :=
    sourceQuadratic_common_squarefree F S₀ cols (fun b hb => (hcols b hb).2) g
      (Finset.mem_filter.mp hg).1
  change (∑ g ∈ D, ‖sourceQuadraticB3Block F S₀ hζ rows cols w a g‖) ≤ _
  calc
    _ ≤ ∑ g ∈ D, B * (R * QuadraticScale.coeffMass (sourceQuadraticDivisibleColumns F S₀ cols g) a) :=
      Finset.sum_le_sum (fun g hg =>
        sourceQuadraticB3Block_norm_le_short F S₀ hζ rows cols w hw a g
          (zero_le_one.trans hN) hG (Finset.mem_filter.mp hg).2.le hcols hdiv)
    _ = (B * R) * ∑ g ∈ D, QuadraticScale.coeffMass (sourceQuadraticDivisibleColumns F S₀ cols g) a := by
      simp only [Finset.mul_sum, mul_assoc]
    _ ≤ (B * R) * (R * QuadraticScale.coeffMass cols a) :=
      mul_le_mul_of_nonneg_left (sourceQuadratic_divisible_mass_sum_le F S₀ cols D a hsf hdiv)
        (mul_nonneg hB hR)
    _ = _ := by
      have hpow : N^(ε / 2) * N^(ε / 2) = N^ε := by
        rw [← Real.rpow_add (zero_lt_one.trans_le hN), add_halves]
      dsimp only [R]
      rw [← hpow]
      ring

end
end ArtinMatthews.SourceEulerAssembly
