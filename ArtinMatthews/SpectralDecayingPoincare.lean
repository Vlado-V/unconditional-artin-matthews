module

public import ArtinMatthews.SpectralCuspAnnularNorm
public import ArtinMatthews.SpectralHeightDecaySummability


set_option backward.privateInPublic true
@[expose] public section

/-! Actual native Poincare vectors for smooth positive-height profiles
with two-sided power decay. They are convergent sums of genuine compact
Poincare seeds, with an explicit exhausting cutoff sequence. -/

noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups ContDiff Topology
namespace ArtinMatthews

structure SpectralDecayingHeightProfile where
  value : ℝ → ℝ
  smooth : ContDiffOn ℝ ∞ value (Ioi (0 : ℝ))
  exponent : ℝ
  exponent_gt_one : 1 < exponent
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  small_bound : ∀ y, 0 < y → ‖value y‖ ≤ bound*y^exponent
  large_bound : ∀ y, 0 < y → ‖value y‖ ≤ bound*y^(-exponent)

def gamma0PrimitiveHeightBlockSeed (N : ℕ) [NeZero N] (a : SL(2, ℤ)) (n : ℤ)
    (P : SpectralDecayingHeightProfile) (A : ℝ) (hA : 0 < A) : h2SmoothCompactSeeds :=
  gamma0PrimitiveFourierPoincareSeed N a n (spectralHeightProfileBlock A P.value)
    (spectralHeightProfileBlock_contDiff hA P.value P.smooth)
    (spectralHeightProfileBlock_compact hA P.value)
    (spectralHeightProfileBlock_positive hA P.value)

def gamma0PrimitiveHeightBlock (N : ℕ) [NeZero N] (a : SL(2, ℤ)) (n : ℤ)
    (P : SpectralDecayingHeightProfile) (A : ℝ) (hA : 0 < A) : Gamma0RegionL2 N :=
  gamma0SmoothSeedMass N (gamma0PrimitiveHeightBlockSeed N a n P A hA)

theorem gamma0PrimitiveHeightBlock_large_norm (N : ℕ) [NeZero N] (a : SL(2, ℤ)) (n : ℤ)
    (P : SpectralDecayingHeightProfile) (A : ℝ) (hA : 0 < A) :
    ‖gamma0PrimitiveHeightBlock N a n P A hA‖ ≤
      gamma0PrimitiveAnnularNormConstant N a*(P.bound*A^(-P.exponent))*(1+2/A) := by
  exact gamma0PrimitiveFourierPoincareTest_annulus_norm_le N a n _
    (spectralHeightProfileBlock_contDiff hA P.value P.smooth)
    (spectralHeightProfileBlock_compact hA P.value)
    (spectralHeightProfileBlock_positive hA P.value) hA
    (mul_nonneg P.bound_nonneg (Real.rpow_nonneg hA.le _))
    (spectralHeightProfileBlock_tsupport hA P.value)
    (spectralHeightProfileBlock_large_bound P.value (by linarith [P.exponent_gt_one])
      P.bound_nonneg hA P.large_bound)

theorem gamma0PrimitiveHeightBlock_small_norm (N : ℕ) [NeZero N] (a : SL(2, ℤ)) (n : ℤ)
    (P : SpectralDecayingHeightProfile) (A : ℝ) (hA : 0 < A) :
    ‖gamma0PrimitiveHeightBlock N a n P A hA‖ ≤
      gamma0PrimitiveAnnularNormConstant N a*(P.bound*(4*A)^P.exponent)*(1+2/A) := by
  exact gamma0PrimitiveFourierPoincareTest_annulus_norm_le N a n _
    (spectralHeightProfileBlock_contDiff hA P.value P.smooth)
    (spectralHeightProfileBlock_compact hA P.value)
    (spectralHeightProfileBlock_positive hA P.value) hA
    (mul_nonneg P.bound_nonneg (Real.rpow_nonneg (by positivity) _))
    (spectralHeightProfileBlock_tsupport hA P.value)
    (spectralHeightProfileBlock_small_bound P.value (by linarith [P.exponent_gt_one])
      P.bound_nonneg hA P.small_bound)

theorem gamma0PrimitiveHeightBlock_large_summable (N : ℕ) [NeZero N] (a : SL(2, ℤ)) (n : ℤ)
    (P : SpectralDecayingHeightProfile) :
    Summable (fun k : ℕ => gamma0PrimitiveHeightBlock N a n P ((2 : ℝ)^k) (by positivity)) := by
  have hs := (spectralHeight_large_budget_summable (by linarith [P.exponent_gt_one] : 0 < P.exponent)).mul_left
    (gamma0PrimitiveAnnularNormConstant N a*P.bound)
  apply hs.of_norm_bounded
  intro k
  exact (gamma0PrimitiveHeightBlock_large_norm N a n P _ (by positivity)).trans_eq (by ring)

theorem gamma0PrimitiveHeightBlock_small_summable (N : ℕ) [NeZero N] (a : SL(2, ℤ)) (n : ℤ)
    (P : SpectralDecayingHeightProfile) :
    Summable (fun k : ℕ => gamma0PrimitiveHeightBlock N a n P (((2 : ℝ)^(k+1))⁻¹) (by positivity)) := by
  have hs := (spectralHeight_small_budget_summable P.exponent_gt_one).mul_left
    (gamma0PrimitiveAnnularNormConstant N a*P.bound)
  apply hs.of_norm_bounded
  intro k
  exact (gamma0PrimitiveHeightBlock_small_norm N a n P _ (by positivity)).trans_eq (by ring)

def gamma0PrimitiveDecayingPoincare (N : ℕ) [NeZero N] (a : SL(2, ℤ)) (n : ℤ)
    (P : SpectralDecayingHeightProfile) : Gamma0RegionL2 N :=
  (∑' k : ℕ, gamma0PrimitiveHeightBlock N a n P ((2 : ℝ)^k) (by positivity))+
    ∑' k : ℕ, gamma0PrimitiveHeightBlock N a n P (((2 : ℝ)^(k+1))⁻¹) (by positivity)

def gamma0PrimitiveDecayingCutoffSeed (N : ℕ) [NeZero N] (a : SL(2, ℤ)) (n : ℤ)
    (P : SpectralDecayingHeightProfile) (K : ℕ) : h2SmoothCompactSeeds :=
  ∑ k ∈ Finset.range (K+1),
    (gamma0PrimitiveHeightBlockSeed N a n P ((2 : ℝ)^k) (by positivity)+
      gamma0PrimitiveHeightBlockSeed N a n P (((2 : ℝ)^(k+1))⁻¹) (by positivity))

theorem gamma0PrimitiveDecayingPoincare_cutoff_tendsto (N : ℕ) [NeZero N]
    (a : SL(2, ℤ)) (n : ℤ) (P : SpectralDecayingHeightProfile) :
    Tendsto (fun K : ℕ => gamma0SmoothSeedMass N (gamma0PrimitiveDecayingCutoffSeed N a n P K))
      atTop (𝓝 (gamma0PrimitiveDecayingPoincare N a n P)) := by
  have h := (gamma0PrimitiveHeightBlock_large_summable N a n P).hasSum.add
    (gamma0PrimitiveHeightBlock_small_summable N a n P).hasSum
  have ht := (tendsto_add_atTop_iff_nat 1).2 h.tendsto_sum_nat
  simpa only [gamma0PrimitiveDecayingCutoffSeed,map_sum,map_add,gamma0PrimitiveHeightBlock,
    gamma0PrimitiveDecayingPoincare] using ht

end ArtinMatthews
