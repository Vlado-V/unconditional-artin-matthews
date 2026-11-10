module

public import ArtinMatthews.SourceQuadraticBlockIdeals
public import ArtinMatthews.SourceQuadraticDiagonalNorm
public import ArtinMatthews.SourceQuadraticPairConductor
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The zero residual in the actual common-ideal block contains only its
diagonal column. Its original coefficient mass is retained. -/

namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain QuadraticScale
open scoped NumberField Classical BigOperators

noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

theorem sourceQuadraticPair_zero_eq_common (b c g : E) (hg : b ⊓ c = g)
    (hz : (b - g) + (c - g) = 0) : b = g ∧ c = g := by
  have hbc := (sourceQuadraticPair_residual_eq_zero_iff F S₀ b c g hg).mp hz
  subst c
  have hbg : b = g := by simpa only [inf_idem] using hg
  exact ⟨hbg, hbg⟩

def sourceQuadraticZeroResidualPairs (cols : Finset E) (g : E) : Finset (E × E) :=
  ((cols ×ˢ cols).filter (fun p => p.1 ⊓ p.2 = g)).filter
    (fun p => (p.1 - g) + (p.2 - g) = 0)

theorem sourceQuadraticZeroResidualPairs_eq (cols : Finset E) (g : E) :
    sourceQuadraticZeroResidualPairs F S₀ cols g = if g ∈ cols then {(g, g)} else ∅ := by
  ext p
  simp only [sourceQuadraticZeroResidualPairs, Finset.mem_filter, Finset.mem_product]
  by_cases hg : g ∈ cols
  · rw [ite_eq_left hg, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨_, hmeet⟩, hzero⟩
      obtain ⟨hb, hc⟩ := sourceQuadraticPair_zero_eq_common F S₀ p.1 p.2 g hmeet hzero
      exact Prod.ext hb hc
    · rintro rfl
      simp only [hg, inf_idem, tsub_self, zero_add, and_self]
  · rw [ite_eq_right hg]
    simp only [Finset.notMem_empty, iff_false]
    rintro ⟨⟨⟨hb, _⟩, hmeet⟩, hzero⟩
    obtain ⟨hbg, _⟩ := sourceQuadraticPair_zero_eq_common F S₀ p.1 p.2 g hmeet hzero
    exact hg (hbg ▸ hb)

def sourceQuadraticZeroResidualBlock (H : E → ℂ) (cols : Finset E) (u : E → ℂ) (g : E) : ℂ :=
  ∑ p ∈ (cols ×ˢ cols).filter (fun p => p.1 ⊓ p.2 = g),
    if (p.1 - g) + (p.2 - g) = 0 then
      star (u p.1) * u p.2 * H ((p.1 - g) + (p.2 - g)) else 0

theorem sourceQuadraticZeroResidualBlock_eq (H : E → ℂ) (cols : Finset E) (u : E → ℂ) (g : E) :
    sourceQuadraticZeroResidualBlock F S₀ H cols u g =
      if g ∈ cols then star (u g) * u g * H 0 else 0 := by
  unfold sourceQuadraticZeroResidualBlock
  rw [← Finset.sum_filter]
  change (∑ p ∈ sourceQuadraticZeroResidualPairs F S₀ cols g,
    star (u p.1) * u p.2 * H ((p.1 - g) + (p.2 - g))) = _
  rw [sourceQuadraticZeroResidualPairs_eq]
  split_ifs <;> simp only [Finset.sum_singleton, tsub_self, zero_add, Finset.sum_empty]

theorem sourceQuadraticZeroResidualBlock_norm_le (H : E → ℂ) (cols : Finset E)
    (u : E → ℂ) (g : E) :
    ‖sourceQuadraticZeroResidualBlock F S₀ H cols u g‖ ≤ ‖H 0‖ * coeffMass cols u := by
  rw [sourceQuadraticZeroResidualBlock_eq]
  by_cases hg : g ∈ cols
  · rw [ite_eq_left hg, norm_mul, norm_mul, norm_star]
    have hmass : ‖u g‖ ^ 2 ≤ coeffMass cols u :=
      Finset.single_le_sum (fun d _ => sq_nonneg ‖u d‖) hg
    calc
      _ = ‖H 0‖ * ‖u g‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass (norm_nonneg _)
  · rw [ite_eq_right hg, norm_zero]
    exact mul_nonneg (norm_nonneg _) (coeffMass_nonneg _ _)

variable [IsTotallyComplex F]

theorem sourceQuadraticDiagonalBlock_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 1 ≤ M → ∀ (cols : Finset E) (u : E → ℂ) (g : E),
      ‖sourceQuadraticZeroResidualBlock F S₀
        (sourceQuadraticBlockIdealFull F S₀ hζ M g) cols u g‖ ≤ C * M * coeffMass cols u ∧
      ∀ K : ℝ, ‖sourceQuadraticZeroResidualBlock F S₀
        (sourceQuadraticBlockRowKernel F S₀ hζ (sourceQuadraticB2Rows F S₀ M K)
          (sourceQuadraticB2RowWeight F S₀ M) g) cols u g‖ ≤ C * M * coeffMass cols u := by
  obtain ⟨C, hC, hbound⟩ := sourceQuadraticDiagonalNorm_bounds F S₀ hζ
  refine ⟨C, hC, ?_⟩
  intro M hM cols u g
  constructor
  · exact (sourceQuadraticZeroResidualBlock_norm_le F S₀ _ cols u g).trans
      (mul_le_mul_of_nonneg_right (hbound M hM g).1 (coeffMass_nonneg _ _))
  · intro K
    exact (sourceQuadraticZeroResidualBlock_norm_le F S₀ _ cols u g).trans
      (mul_le_mul_of_nonneg_right ((hbound M hM g).2 K) (coeffMass_nonneg _ _))

theorem sourceQuadraticDiagonalBlock_b3_scale :
    ∃ C : ℝ, 0 < C ∧ ∀ M P : ℝ, 1 ≤ M → 0 ≤ P →
      ∀ (cols : Finset E) (u : E → ℂ) (g : E),
      ‖sourceQuadraticZeroResidualBlock F S₀
        (sourceQuadraticBlockIdealFull F S₀ hζ M g) cols u g‖ ≤
          C * (q g : ℝ) ^ 4 * (M + P) * coeffMass cols u ∧
      ∀ K : ℝ, ‖sourceQuadraticZeroResidualBlock F S₀
        (sourceQuadraticBlockRowKernel F S₀ hζ (sourceQuadraticB2Rows F S₀ M K)
          (sourceQuadraticB2RowWeight F S₀ M) g) cols u g‖ ≤
          C * (q g : ℝ) ^ 4 * (M + P) * coeffMass cols u := by
  obtain ⟨C, hC, hbound⟩ := sourceQuadraticDiagonalBlock_bounds F S₀ hζ
  refine ⟨C, hC, ?_⟩
  intro M P hM hP cols u g
  have hq : (1 : ℝ) ≤ (q g : ℝ) ^ 4 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
      (sourceReflection_norm_one_le F S₀ g) 4
  have hscale : M ≤ (q g : ℝ) ^ 4 * (M + P) := by
    calc
      M ≤ M + P := le_add_of_nonneg_right hP
      _ = 1 * (M + P) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hq (by linarith)
  have hfinal : C * M * coeffMass cols u ≤ C * (q g : ℝ) ^ 4 * (M + P) * coeffMass cols u := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hscale hC.le) (coeffMass_nonneg cols u)
  exact ⟨((hbound M hM cols u g).1).trans hfinal,
    fun K => ((hbound M hM cols u g).2 K).trans hfinal⟩

theorem sourceQuadraticDiagonalFullSubSmall_eq {M K : ℝ} (hM : 0 < M)
    (cols : Finset E) (u : E → ℂ) (g : E) :
    sourceQuadraticZeroResidualBlock F S₀
      (fun e => sourceQuadraticBlockIdealFull F S₀ hζ M g e -
        sourceQuadraticBlockIdealSmall F S₀ hζ M K g e) cols u g =
      sourceQuadraticZeroResidualBlock F S₀
        (sourceQuadraticBlockRowKernel F S₀ hζ (sourceQuadraticB2Rows F S₀ M K)
          (sourceQuadraticB2RowWeight F S₀ M) g) cols u g := by
  have he : sourceReflectionIsSquarefree (0 : E) := by
    intro P
    simp only [Finsupp.zero_apply, zero_le_one]
  have hzero := (sourceQuadraticBlockRowKernel_eq_idealTail F S₀ hζ (K := K) hM g 0 he).trans
    (sourceQuadraticBlockIdealTail_eq_full_sub_small F S₀ hζ (K := K) hM g 0 he)
  rw [sourceQuadraticZeroResidualBlock_eq, sourceQuadraticZeroResidualBlock_eq]
  rw [hzero]

theorem sourceQuadraticDiagonalFullSubSmall_b3_scale :
    ∃ C : ℝ, 0 < C ∧ ∀ M P K : ℝ, 1 ≤ M → 0 ≤ P →
      ∀ (cols : Finset E) (u : E → ℂ) (g : E),
      ‖sourceQuadraticZeroResidualBlock F S₀
        (fun e => sourceQuadraticBlockIdealFull F S₀ hζ M g e -
          sourceQuadraticBlockIdealSmall F S₀ hζ M K g e) cols u g‖ ≤
            C * (q g : ℝ) ^ 4 * (M + P) * coeffMass cols u := by
  obtain ⟨C, hC, hbound⟩ := sourceQuadraticDiagonalBlock_b3_scale F S₀ hζ
  refine ⟨C, hC, ?_⟩
  intro M P K hM hP cols u g
  rw [sourceQuadraticDiagonalFullSubSmall_eq F S₀ hζ (zero_lt_one.trans_le hM) cols u g]
  exact (hbound M P hM hP cols u g).2 K

end
end ArtinMatthews.SourceEulerAssembly
