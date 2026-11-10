module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition


set_option backward.privateInPublic true
@[expose] public section

/-! A concrete positive dyadic partition of the positive height axis.
Finite partial sums are compact cutoffs and are eventually one at every
positive height. Each individual block lies in a fourfold annulus. -/

noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ArtinMatthews

def spectralHeightCutStep (y : ℝ) : ℝ := Real.smoothTransition (y-1)

theorem spectralHeightCutStep_zero {y : ℝ} (hy : y ≤ 1) : spectralHeightCutStep y = 0 :=
  Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hy)

theorem spectralHeightCutStep_one {y : ℝ} (hy : 2 ≤ y) : spectralHeightCutStep y = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem spectralHeightCutStep_nonneg (y : ℝ) : 0 ≤ spectralHeightCutStep y :=
  Real.smoothTransition.nonneg _

theorem spectralHeightCutStep_le_one (y : ℝ) : spectralHeightCutStep y ≤ 1 :=
  Real.smoothTransition.le_one _

def spectralHeightAnnularBlock (A y : ℝ) : ℝ :=
  spectralHeightCutStep (y/A)-spectralHeightCutStep (y/(2*A))

theorem spectralHeightAnnularBlock_zero_low {A y : ℝ} (hA : 0 < A) (hy : y ≤ A) :
    spectralHeightAnnularBlock A y = 0 := by
  rw [spectralHeightAnnularBlock,spectralHeightCutStep_zero ((div_le_one hA).mpr hy),
    spectralHeightCutStep_zero ((div_le_one (by positivity : 0 < 2*A)).mpr (by linarith))]
  ring

theorem spectralHeightAnnularBlock_zero_high {A y : ℝ} (hA : 0 < A) (hy : 4*A ≤ y) :
    spectralHeightAnnularBlock A y = 0 := by
  rw [spectralHeightAnnularBlock,spectralHeightCutStep_one ((le_div_iff₀ hA).mpr (by linarith)),
    spectralHeightCutStep_one ((le_div_iff₀ (by positivity : 0 < 2*A)).mpr (by linarith))]
  ring

theorem spectralHeightAnnularBlock_bounds {A : ℝ} (hA : 0 < A) (y : ℝ) :
    0 ≤ spectralHeightAnnularBlock A y ∧ spectralHeightAnnularBlock A y ≤ 1 := by
  by_cases hy : y ≤ A
  · rw [spectralHeightAnnularBlock_zero_low hA hy]
    norm_num
  have hy0 : 0 ≤ y := hA.le.trans (le_of_not_ge hy)
  have hle : y/(2*A) ≤ y/A :=
    div_le_div_of_nonneg_left hy0 hA (by linarith)
  have hm : spectralHeightCutStep (y/(2*A)) ≤ spectralHeightCutStep (y/A) :=
    Real.smoothTransition.monotone (sub_le_sub_right hle 1)
  unfold spectralHeightAnnularBlock
  constructor
  · exact sub_nonneg.mpr hm
  · linarith [spectralHeightCutStep_nonneg (y/(2*A)),spectralHeightCutStep_le_one (y/A)]

theorem spectralHeightAnnularBlock_contDiff (A : ℝ) :
    ContDiff ℝ ∞ (spectralHeightAnnularBlock A) := by
  unfold spectralHeightAnnularBlock spectralHeightCutStep
  fun_prop

theorem spectralHeightAnnularBlock_tsupport {A : ℝ} (hA : 0 < A) :
    tsupport (spectralHeightAnnularBlock A) ⊆ Icc A (4*A) := by
  apply closure_minimal _ isClosed_Icc
  intro y hy
  constructor
  · by_contra! h
    exact hy (spectralHeightAnnularBlock_zero_low hA h.le)
  · by_contra! h
    exact hy (spectralHeightAnnularBlock_zero_high hA h.le)

theorem spectralHeightAnnularBlock_compact {A : ℝ} (hA : 0 < A) :
    HasCompactSupport (spectralHeightAnnularBlock A) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (spectralHeightAnnularBlock_tsupport hA)

theorem spectralHeightAnnularBlock_pow (k : ℕ) (y : ℝ) :
    spectralHeightAnnularBlock ((2 : ℝ)^k) y =
      spectralHeightCutStep (y/(2 : ℝ)^k)-spectralHeightCutStep (y/(2 : ℝ)^(k+1)) := by
  simp only [spectralHeightAnnularBlock,pow_succ,mul_comm (2 : ℝ)]

theorem spectralHeightAnnularBlock_inv_pow (k : ℕ) (y : ℝ) :
    spectralHeightAnnularBlock (((2 : ℝ)^(k+1))⁻¹) y =
      spectralHeightCutStep ((2 : ℝ)^(k+1)*y)-spectralHeightCutStep ((2 : ℝ)^k*y) := by
  have he : y/(2*((2 : ℝ)^(k+1))⁻¹) = (2 : ℝ)^k*y := by
    rw [pow_succ]
    field_simp
  simp only [spectralHeightAnnularBlock,div_inv_eq_mul,he,mul_comm y]

def spectralHeightAnnularPartial (K : ℕ) (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (K+1),
    (spectralHeightAnnularBlock ((2 : ℝ)^k) y+
      spectralHeightAnnularBlock (((2 : ℝ)^(k+1))⁻¹) y)

theorem spectralHeightAnnularPartial_eq (K : ℕ) (y : ℝ) :
    spectralHeightAnnularPartial K y =
      spectralHeightCutStep ((2 : ℝ)^(K+1)*y)-spectralHeightCutStep (y/(2 : ℝ)^(K+1)) := by
  induction K with
  | zero =>
      simp only [spectralHeightAnnularPartial,Finset.sum_range_succ,Finset.sum_range_zero,
        spectralHeightAnnularBlock_pow,spectralHeightAnnularBlock_inv_pow,zero_add,pow_zero,one_mul,div_one]
      ring
  | succ K ih =>
      change (∑ k ∈ Finset.range ((K+1)+1), _) = _
      rw [Finset.sum_range_succ]
      change spectralHeightAnnularPartial K y+_ = _
      rw [ih,spectralHeightAnnularBlock_pow,spectralHeightAnnularBlock_inv_pow]
      ring

theorem spectralHeightAnnularPartial_bounds (K : ℕ) (y : ℝ) :
    0 ≤ spectralHeightAnnularPartial K y ∧ spectralHeightAnnularPartial K y ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg (fun k _ => add_nonneg
      (spectralHeightAnnularBlock_bounds (by positivity) y).1
      (spectralHeightAnnularBlock_bounds (by positivity) y).1)
  · rw [spectralHeightAnnularPartial_eq]
    linarith [spectralHeightCutStep_le_one ((2 : ℝ)^(K+1)*y),
      spectralHeightCutStep_nonneg (y/(2 : ℝ)^(K+1))]

theorem spectralHeightAnnularPartial_eventually_one {y : ℝ} (hy : 0 < y) :
    ∀ᶠ K : ℕ in atTop, spectralHeightAnnularPartial K y = 1 := by
  have hp : Tendsto (fun K : ℕ => (2 : ℝ)^(K+1)) atTop atTop :=
    (tendsto_add_atTop_iff_nat 1).2 (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  filter_upwards [hp.eventually_ge_atTop (max (2/y) y)] with K hK
  rw [spectralHeightAnnularPartial_eq,spectralHeightCutStep_one,spectralHeightCutStep_zero]
  · norm_num
  · exact (div_le_one (by positivity : 0 < (2 : ℝ)^(K+1))).mpr ((le_max_right _ _).trans hK)
  · exact (div_le_iff₀ hy).mp ((le_max_left _ _).trans hK)

end ArtinMatthews
