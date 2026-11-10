module

public import ArtinMatthews.SourceQuadraticB3SquarefreeTail
public import ArtinMatthews.SourceQuadraticClassFactorization
public import ArtinMatthews.SourceQuadraticB3PairMass
public import ArtinMatthews.SourceQuadraticB3WeightedTailScale
public import ArtinMatthews.SourceQuadraticClassPair
public import ArtinMatthews.SourceQuadraticSquarefreePairTail
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

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain QuadraticScale
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

/-- Pair counting converts the genuine squarefree tail into the raw B3 tail scale. -/
theorem sourceQuadraticB3SquarefreeTail_raw_bound (σ : ℝ) (hσ : 2 ≤ σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M P K : ℝ), 0 < M → 1 ≤ P → 0 < K →
      ∀ cols : Finset E, (∀ b ∈ cols, sourceReflectionIsSquarefree b) →
      (∀ b ∈ cols, (q b : ℝ) ≤ 2 * P) →
      ∀ (κ : SourceQuadraticRayClass F S₀) (g : E) (a : E → ℂ),
      let D := sourceQuadraticClassColumns F S₀ cols (sourcePrimeExponentRayClass F S₀) κ
      ‖sourceQuadraticB3SquarefreeTail F S₀ hζ M K D a g‖ ≤
        C * (q g : ℝ) ^ 4 *
          (P * (M ^ (1 - σ) * P ^ (2 * σ - 1) * K ^ (2 - σ))) * coeffMass D a := by
  obtain ⟨A, hA, hmass⟩ := sourceQuadraticPairMass_bound F S₀
  obtain ⟨B, hB, hpair⟩ := sourceQuadraticSquarefreePairTail_bound F S₀ hζ σ hσ
  refine ⟨B * A, mul_nonneg hB hA.le, ?_⟩
  intro M P K hM hP hK cols hcols hnorm κ g a
  let D := sourceQuadraticClassColumns F S₀ cols (sourcePrimeExponentRayClass F S₀) κ
  let pairs := (D ×ˢ D).filter (fun p : E × E => p.1 ⊓ p.2 = g ∧ p.1 ≠ p.2)
  let R := M ^ (1 - σ) * P ^ (2 * σ - 1) * K ^ (2 - σ)
  change ‖sourceQuadraticB3SquarefreeTail F S₀ hζ M K D a g‖ ≤
    (B * A) * (q g : ℝ) ^ 4 * (P * R) * coeffMass D a
  have hD (b : E) (hb : b ∈ D) : (q b : ℝ) ≤ 2 * P :=
    hnorm b (Finset.mem_filter.mp hb).1
  have hpbound (p : E × E) (hp : p ∈ pairs) :
      ‖sourceQuadraticDualDivisorTail F S₀ hζ M K g ((p.1 - g) + (p.2 - g))‖ ≤
        B * (q g : ℝ) ^ 4 * R := by
    obtain ⟨hpD, hpg, _⟩ := Finset.mem_filter.mp hp
    have hpcommon : p ∈ (D ×ˢ D).filter (fun p : E × E => p.1 ⊓ p.2 = g) :=
      Finset.mem_filter.mpr ⟨hpD, hpg⟩
    obtain ⟨hb, hc, hg, hclass⟩ := sourceQuadraticClassPair_mem F S₀ cols
      (sourcePrimeExponentRayClass F S₀) κ p g hpcommon
    rw [← sourceQuadraticBlockSquarefreeTail_eq_divisorTail F S₀ hζ M K g]
    exact hpair M P K hM (zero_lt_one.trans_le hP) hK p.1 p.2 g
      (hcols p.1 hb) (hcols p.2 hc) hg
      (sourcePrimeExponentRayClass_eq_localClass F S₀ hζ p.1 p.2 hclass)
      (hnorm p.1 hb) (hnorm p.2 hc)
  have hm := hmass P hP D hD pairs (Finset.filter_subset _ _) a
  have hfactor : 0 ≤ B * (q g : ℝ) ^ 4 * R := by
    dsimp only [R]
    positivity
  change ‖∑ p ∈ pairs, star (a p.1) * a p.2 *
      sourceQuadraticDualDivisorTail F S₀ hζ M K g ((p.1 - g) + (p.2 - g))‖ ≤ _
  calc
    _ ≤ ∑ p ∈ pairs, ‖star (a p.1) * a p.2‖ *
        ‖sourceQuadraticDualDivisorTail F S₀ hζ M K g ((p.1 - g) + (p.2 - g))‖ := by
      simpa only [norm_mul] using norm_sum_le pairs (fun p => star (a p.1) * a p.2 *
        sourceQuadraticDualDivisorTail F S₀ hζ M K g ((p.1 - g) + (p.2 - g)))
    _ ≤ ∑ p ∈ pairs, ‖star (a p.1) * a p.2‖ * (B * (q g : ℝ) ^ 4 * R) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (hpbound p hp) (norm_nonneg _)
    _ = (B * (q g : ℝ) ^ 4 * R) * ∑ p ∈ pairs, ‖star (a p.1) * a p.2‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ (B * (q g : ℝ) ^ 4 * R) * (A * P * coeffMass D a) :=
      mul_le_mul_of_nonneg_left hm hfactor
    _ = _ := by ring

/-- The aggregate tail fits the original B3 scale with the same common-ideal exponent. -/
theorem sourceQuadraticB3SquarefreeTail_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M P K : ℝ), 1 ≤ M → 1 ≤ P →
      P ^ 2 / M * (M * P) ^ δ ≤ K → K ≤ M * (M * P) ^ (-δ) →
      ∀ cols : Finset E, (∀ b ∈ cols, sourceReflectionIsSquarefree b) →
      (∀ b ∈ cols, (q b : ℝ) ≤ 2 * P) →
      ∀ (κ : SourceQuadraticRayClass F S₀) (g : E) (a : E → ℂ) (α : ℝ),
      let D := sourceQuadraticClassColumns F S₀ cols (sourcePrimeExponentRayClass F S₀) κ
      ‖sourceQuadraticB3SquarefreeTail F S₀ hζ M K D a g‖ ≤
        (C * (q g : ℝ) ^ 4 * (M * P) ^ δ *
          (M + P + Real.sqrt M * K ^ (α - 1 / 2) + Real.sqrt (M / K) * P)) *
            coeffMass D a := by
  obtain ⟨C, hC, hraw⟩ := sourceQuadraticB3SquarefreeTail_raw_bound F S₀ hζ
    (quadraticB3TailLine δ) (quadraticB3TailLine_ge_two hδ)
  refine ⟨C, hC, ?_⟩
  intro M P K hM hP hlower hupper cols hcols hnorm κ g a α
  let D := sourceQuadraticClassColumns F S₀ cols (sourcePrimeExponentRayClass F S₀) κ
  have hK := (quadraticB3_cutoff_range hM hP hδ hlower hupper).1
  exact (hraw M P K (zero_lt_one.trans_le hM) hP hK cols hcols hnorm κ g a).trans
    (sourceQuadraticB3_weighted_tail_to_block F S₀ hM hP hδ hlower hupper
      C hC g D a α)

end
end ArtinMatthews.SourceEulerAssembly
