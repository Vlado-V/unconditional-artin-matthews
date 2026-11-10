module

public import ArtinMatthews.CircleDetector
public import ArtinMatthews.CircleNormalizerDefinitions
public import ArtinMatthews.CircleNormalizerBlocks
public import ArtinMatthews.CircleNormalizerTotient
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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


set_option backward.privateInPublic true
@[expose] public section

/-! A near-optimal lower bound for the actual totient-weighted circle
normalizer. Complete reduced-residue blocks are used only as a lower-bound
subset of the original all-moduli family. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators

theorem circleNormalizer_lower (ε : ℝ) (hε : 0 < ε) (hεone : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ F r L : ℕ, 0 < F → 0 < r → F.Coprime r →
      4 * (F * r) ≤ L → ∀ ω : ℕ → ℝ,
      (∀ q ∈ circleModuli F r L, 0 ≤ ω q) →
      (∀ q : ℕ, 4 * L ≤ q → q ≤ 5 * L → 1 ≤ ω q) →
      C * (L : ℝ) ^ (2 - ε) / ((F : ℝ) * (r : ℝ)^ε) ≤
        circleNormalizer (circleModuli F r L) ω := by
  obtain ⟨c, hc, hφ⟩ := circle_totient_ge_rpow ε hε
  refine ⟨c^2/4, by positivity, ?_⟩
  intro F r L hF hr hFr hL ω hω hplateau
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity : 0 < 4 * (F * r)) hL
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hFR : (0 : ℝ) < F := by exact_mod_cast hF
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hsub := circlePlateauModuli_subset hF hr hFr hL
  have hpoint : ∀ q ∈ circlePlateauModuli F r L,
      c * (L : ℝ)^(1-ε) ≤ ω q * (q.totient : ℝ) := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hqlow, hqhigh⟩ := circleBlockModulus_plateau hF hr hL hp
    have hqL : L ≤ circleBlockModulus F r L p := by omega
    have hqpos : 0 < circleBlockModulus F r L p := lt_of_lt_of_le hLpos hqL
    calc
      _ ≤ c * (circleBlockModulus F r L p : ℝ)^(1-ε) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg L) (by exact_mod_cast hqL) (by linarith)) hc.le
      _ ≤ _ := hφ _ hqpos
      _ ≤ _ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (hplateau _ hqlow hqhigh) (Nat.cast_nonneg (circleBlockModulus F r L p).totient)
  have hsum : ((circlePlateauModuli F r L).card : ℝ) * (c * (L : ℝ)^(1-ε)) ≤
      circleNormalizer (circleModuli F r L) ω := by
    calc
      _ = ∑ _q ∈ circlePlateauModuli F r L, c * (L : ℝ)^(1-ε) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ q ∈ circlePlateauModuli F r L, ω q * (q.totient : ℝ) :=
        Finset.sum_le_sum hpoint
      _ ≤ ∑ q ∈ circleModuli F r L, ω q * (q.totient : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun q hq _ => mul_nonneg (hω q hq) (Nat.cast_nonneg _))
      _ = _ := rfl
  have hB : (L : ℝ) / (4 * ((F * r : ℕ) : ℝ)) ≤ circleBlockLength F r L := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * ((F * r : ℕ) : ℝ))).mpr
    have hcast : (L : ℝ) ≤ 4 * ((F * r : ℕ) : ℝ) * circleBlockLength F r L := by
      exact_mod_cast circleBlockLength_lower hF hr hL
    nlinarith
  have hcard : ((L : ℝ) / (4 * ((F * r : ℕ) : ℝ))) * (c * (r : ℝ)^(1-ε)) ≤
      ((circlePlateauModuli F r L).card : ℝ) := by
    rw [circlePlateauModuli_card hF hr]
    simpa only [Nat.cast_mul] using
      mul_le_mul hB (hφ r hr) (by positivity) (Nat.cast_nonneg _)
  have hLpow : (L : ℝ)^(2-ε) = (L : ℝ) * (L : ℝ)^(1-ε) := by
    rw [show (2 : ℝ)-ε = 1+(1-ε) by ring, Real.rpow_add hLR, Real.rpow_one]
  have hrpow : (r : ℝ)^(1-ε) = (r : ℝ)/(r : ℝ)^ε := by
    rw [Real.rpow_sub hrR, Real.rpow_one]
  have heq : (((L : ℝ) / (4 * ((F * r : ℕ) : ℝ))) * (c * (r : ℝ)^(1-ε))) *
      (c * (L : ℝ)^(1-ε)) =
      (c^2/4) * (L : ℝ)^(2-ε) / ((F : ℝ) * (r : ℝ)^ε) := by
    rw [hrpow, hLpow, Nat.cast_mul]
    field_simp
  rw [← heq]
  exact (mul_le_mul_of_nonneg_right hcard (by positivity)).trans hsum

theorem circleNormalizer_positive {F r L : ℕ} (hF : 0 < F) (hr : 0 < r)
    (hFr : F.Coprime r) (hL : 4 * (F * r) ≤ L) (ω : ℕ → ℝ)
    (hω : ∀ q ∈ circleModuli F r L, 0 ≤ ω q)
    (hplateau : ∀ q : ℕ, 4 * L ≤ q → q ≤ 5 * L → 1 ≤ ω q) :
    0 < circleNormalizer (circleModuli F r L) ω := by
  obtain ⟨C, hC, hbound⟩ := circleNormalizer_lower (1/2) (by norm_num) (by norm_num)
  have hlower := hbound F r L hF hr hFr hL ω hω hplateau
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity : 0 < 4 * (F * r)) hL
  exact lt_of_lt_of_le (by positivity) hlower

end ArtinMatthews
