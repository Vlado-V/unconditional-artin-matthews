module

public import ArtinMatthews.SpectralKLCosineDifferenceData


set_option backward.privateInPublic true
@[expose] public section

/-! Explicit smooth compact cutoffs of the actual cosine-difference data.
They converge in the literal spectral L2 space. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace ArtinMatthews

def spectralKLRangeCutoff (n : ℕ) (t : ℝ) : ℝ :=
  spectralKLPositiveCutoff n t*Real.smoothTransition ((n : ℝ)+2-t)

theorem spectralKLRangeCutoff_contDiff (n : ℕ) :
    ContDiff ℝ ∞ (fun t : ℝ => (spectralKLRangeCutoff n t : ℂ)) := by
  have hc : ContDiff ℝ ∞ (spectralKLRangeCutoff n) := by
    unfold spectralKLRangeCutoff spectralKLPositiveCutoff
    fun_prop
  exact Complex.ofRealCLM.contDiff.comp hc

theorem spectralKLRangeCutoff_bounds (n : ℕ) (t : ℝ) :
    0 ≤ spectralKLRangeCutoff n t ∧ spectralKLRangeCutoff n t ≤ 1 := by
  have ha := Real.smoothTransition.nonneg (((n : ℝ)+1)*t-1)
  have hb := Real.smoothTransition.le_one (((n : ℝ)+1)*t-1)
  have hc := Real.smoothTransition.nonneg ((n : ℝ)+2-t)
  have hd := Real.smoothTransition.le_one ((n : ℝ)+2-t)
  unfold spectralKLRangeCutoff spectralKLPositiveCutoff
  constructor
  · exact mul_nonneg ha hc
  · nlinarith

theorem spectralKLRangeCutoff_tsupport (n : ℕ) :
    tsupport (fun t : ℝ => (spectralKLRangeCutoff n t : ℂ)) ⊆ Ioi (0 : ℝ) := by
  have heq : (fun t : ℝ => (spectralKLRangeCutoff n t : ℂ)) =
      (fun t : ℝ => (spectralKLPositiveCutoff n t : ℂ)*(Real.smoothTransition ((n : ℝ)+2-t) : ℂ)) := by
    funext t
    exact Complex.ofReal_mul _ _
  rw [heq]
  exact tsupport_mul_subset_left.trans (spectralKLPositiveCutoff_tsupport n)

theorem spectralKLRangeCutoff_hasCompactSupport (n : ℕ) :
    HasCompactSupport (fun t : ℝ => (spectralKLRangeCutoff n t : ℂ)) := by
  have hu : tsupport (fun t : ℝ => (spectralKLRangeCutoff n t : ℂ)) ⊆ Iic ((n : ℝ)+2) := by
    unfold tsupport
    apply closure_minimal _ isClosed_Iic
    intro t ht
    by_contra hn
    have harg : (n : ℝ)+2-t ≤ 0 := by simp only [mem_Iic] at hn; linarith
    exact (Function.mem_support.mp ht) (by
      unfold spectralKLRangeCutoff
      rw [Real.smoothTransition.zero_of_nonpos harg,mul_zero,Complex.ofReal_zero])
  change IsCompact _
  apply isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
  intro t ht
  exact ⟨(spectralKLRangeCutoff_tsupport n ht).le,hu ht⟩

theorem spectralKLRangeCutoff_eventually_one {t : ℝ} (ht : 0 < t) :
    ∀ᶠ n : ℕ in atTop, spectralKLRangeCutoff n t = 1 := by
  have hu : ∀ᶠ n : ℕ in atTop, Real.smoothTransition ((n : ℝ)+2-t) = 1 := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (t-1))] with n hn
    apply Real.smoothTransition.one_of_one_le
    linarith
  filter_upwards [hu,spectralKLPositiveCutoff_eventually_one ht] with n hn hp
  simp only [spectralKLRangeCutoff,hn,hp,one_mul]

def spectralKLCosineDifferenceCutoff (u v : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  (spectralKLRangeCutoff n t : ℂ)*spectralKLCosineDifferenceData u v t

theorem spectralKLCosineDifferenceCutoff_test (u v : ℝ) (n : ℕ) :
    spectralKLCosineDifferenceCutoff u v n ∈ spectralKLTestSubmodule := by
  have hp : tsupport (spectralKLCosineDifferenceCutoff u v n) ⊆ Ioi (0 : ℝ) :=
    tsupport_mul_subset_left.trans (spectralKLRangeCutoff_tsupport n)
  have hc : HasCompactSupport (spectralKLCosineDifferenceCutoff u v n) :=
    (spectralKLRangeCutoff_hasCompactSupport n).mul_right
  have hd : ContDiffOn ℝ ∞ (spectralKLCosineDifferenceCutoff u v n) (Ioi (0 : ℝ)) :=
    (spectralKLRangeCutoff_contDiff n).contDiffOn.mul (spectralKLCosineDifferenceData_contDiffOn u v)
  refine ⟨?_,hc,hp⟩
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : 0 < t
  · exact hd.contDiffAt (isOpen_Ioi.mem_nhds ht)
  · have hn : t ∉ tsupport (spectralKLCosineDifferenceCutoff u v n) := fun h => ht (hp h)
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hn)

def spectralKLCosineDifferenceTest (u v : ℝ) (n : ℕ) : spectralKLTestSubmodule :=
  ⟨spectralKLCosineDifferenceCutoff u v n,spectralKLCosineDifferenceCutoff_test u v n⟩

theorem spectralKLCosineDifferenceTest_tendsto (u v : ℝ) :
    Tendsto (fun n => spectralKLTestToLp (spectralKLCosineDifferenceTest u v n)) atTop
      (𝓝 ((spectralKLCosineDifferenceData_memLp u v).toLp (spectralKLCosineDifferenceData u v))) := by
  have hmem (n : ℕ) : MemLp (spectralKLCosineDifferenceCutoff u v n) 2 spectralKLSpectralMeasure :=
    spectralKLSpectralMeasure_memLp_compact _ (spectralKLCosineDifferenceCutoff_test u v n).1.continuous
      (spectralKLCosineDifferenceCutoff_test u v n).2.1
  change Tendsto (fun n => (hmem n).toLp (spectralKLCosineDifferenceCutoff u v n)) atTop _
  apply spectral_L2_toLp_tendsto_of_dominated _ hmem _ (spectralKLCosineDifferenceData_memLp u v)
    (fun t => 4*‖spectralKLCosineDifferenceData u v t‖^2)
    (((memLp_two_iff_integrable_sq_norm (spectralKLCosineDifferenceData_memLp u v).aestronglyMeasurable).mp
      (spectralKLCosineDifferenceData_memLp u v)).const_mul 4)
  · intro n
    filter_upwards with t
    have hη : ‖(spectralKLRangeCutoff n t : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real,Real.norm_of_nonneg (spectralKLRangeCutoff_bounds n t).1]
      exact (spectralKLRangeCutoff_bounds n t).2
    have hbd : ‖spectralKLCosineDifferenceCutoff u v n t-spectralKLCosineDifferenceData u v t‖ ≤
        2*‖spectralKLCosineDifferenceData u v t‖ := by
      calc
        _ ≤ ‖spectralKLCosineDifferenceCutoff u v n t‖+‖spectralKLCosineDifferenceData u v t‖ := norm_sub_le _ _
        _ ≤ ‖spectralKLCosineDifferenceData u v t‖+‖spectralKLCosineDifferenceData u v t‖ := by
          unfold spectralKLCosineDifferenceCutoff
          rw [norm_mul]
          exact add_le_add (mul_le_of_le_one_left (norm_nonneg (spectralKLCosineDifferenceData u v t)) hη) le_rfl
        _ = _ := by ring
    nlinarith [norm_nonneg (spectralKLCosineDifferenceCutoff u v n t-spectralKLCosineDifferenceData u v t),
      norm_nonneg (spectralKLCosineDifferenceData u v t)]
  · filter_upwards [spectralKLPositiveWeightMeasure_ae_pos spectralKLPlancherelWeight] with t ht
    apply tendsto_const_nhds.congr'
    filter_upwards [spectralKLRangeCutoff_eventually_one ht] with n hn
    simp [spectralKLCosineDifferenceCutoff,hn]

end ArtinMatthews
