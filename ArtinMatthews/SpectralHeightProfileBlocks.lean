module

public import ArtinMatthews.SpectralHeightAnnularPartition


set_option backward.privateInPublic true
@[expose] public section

/-! Compact smooth annular pieces of a profile that is smooth only at
positive heights. No smooth extension across height zero is required. -/

noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ArtinMatthews

def spectralHeightProfileBlock (A : ℝ) (ρ : ℝ → ℝ) (y : ℝ) : ℝ :=
  spectralHeightAnnularBlock A y*ρ y

theorem spectralHeightProfileBlock_contDiff {A : ℝ} (hA : 0 < A) (ρ : ℝ → ℝ)
    (hρ : ContDiffOn ℝ ∞ ρ (Ioi (0 : ℝ))) :
    ContDiff ℝ ∞ (spectralHeightProfileBlock A ρ) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : 0 < y
  · exact (spectralHeightAnnularBlock_contDiff A).contDiffAt.mul
      (hρ.contDiffAt (Ioi_mem_nhds hy))
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ((le_of_not_gt hy).trans_lt hA)] with z hz
    rw [spectralHeightProfileBlock,spectralHeightAnnularBlock_zero_low hA hz.le,zero_mul]

theorem spectralHeightProfileBlock_tsupport {A : ℝ} (hA : 0 < A) (ρ : ℝ → ℝ) :
    tsupport (spectralHeightProfileBlock A ρ) ⊆ Icc A (4*A) :=
  (tsupport_mul_subset_left (f := spectralHeightAnnularBlock A) (g := ρ)).trans
    (spectralHeightAnnularBlock_tsupport hA)

theorem spectralHeightProfileBlock_compact {A : ℝ} (hA : 0 < A) (ρ : ℝ → ℝ) :
    HasCompactSupport (spectralHeightProfileBlock A ρ) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (spectralHeightProfileBlock_tsupport hA ρ)

theorem spectralHeightProfileBlock_positive {A : ℝ} (hA : 0 < A) (ρ : ℝ → ℝ) :
    tsupport (spectralHeightProfileBlock A ρ) ⊆ Ioi (0 : ℝ) :=
  fun _ hy => hA.trans_le ((spectralHeightProfileBlock_tsupport hA ρ) hy).1

theorem spectralHeightProfileBlock_norm_le {A M : ℝ} (hA : 0 < A) (hM : 0 ≤ M)
    (ρ : ℝ → ℝ) (hb : ∀ y ∈ Icc A (4*A), ‖ρ y‖ ≤ M) (y : ℝ) :
    ‖spectralHeightProfileBlock A ρ y‖ ≤ M := by
  by_cases hz : spectralHeightAnnularBlock A y = 0
  · simp only [spectralHeightProfileBlock,hz,zero_mul,norm_zero]
    exact hM
  have hy := spectralHeightAnnularBlock_tsupport hA (subset_tsupport _ hz)
  rw [spectralHeightProfileBlock,norm_mul,Real.norm_eq_abs,
    abs_of_nonneg (spectralHeightAnnularBlock_bounds hA y).1]
  exact (mul_le_mul_of_nonneg_right (spectralHeightAnnularBlock_bounds hA y).2 (norm_nonneg _)).trans
    (by simpa only [one_mul] using hb y hy)

theorem spectralHeightProfileBlock_partial (ρ : ℝ → ℝ) (K : ℕ) (y : ℝ) :
    (∑ k ∈ Finset.range (K+1),
      (spectralHeightProfileBlock ((2 : ℝ)^k) ρ y+
        spectralHeightProfileBlock (((2 : ℝ)^(k+1))⁻¹) ρ y)) =
      spectralHeightAnnularPartial K y*ρ y := by
  simp only [spectralHeightProfileBlock,← add_mul,spectralHeightAnnularPartial,Finset.sum_mul]

theorem spectralHeightProfileBlock_partial_eventually (ρ : ℝ → ℝ) {y : ℝ} (hy : 0 < y) :
    ∀ᶠ K : ℕ in atTop,
      (∑ k ∈ Finset.range (K+1),
        (spectralHeightProfileBlock ((2 : ℝ)^k) ρ y+
          spectralHeightProfileBlock (((2 : ℝ)^(k+1))⁻¹) ρ y)) = ρ y := by
  filter_upwards [spectralHeightAnnularPartial_eventually_one hy] with K hK
  rw [spectralHeightProfileBlock_partial,hK,one_mul]

end ArtinMatthews
