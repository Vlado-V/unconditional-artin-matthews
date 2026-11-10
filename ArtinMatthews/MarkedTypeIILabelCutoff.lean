module

public import ArtinMatthews.SpectralDyadicWeight
public import Mathlib.Analysis.SpecialFunctions.Pow.Real


set_option backward.privateInPublic true
@[expose] public section

/-! A literal real smooth label cutoff supported on [1,4], with the
exact dyadic telescoping identity used before the marked Cauchy square. -/
namespace ArtinMatthews
open scoped BigOperators ContDiff
noncomputable section

def markedTypeIILabelCutoffReal (t : ℝ) : ℝ :=
  spectralDyadicStep t-spectralDyadicStep (t/2)

def markedTypeIILabelCutoff (t : ℝ) : ℂ := markedTypeIILabelCutoffReal t

theorem markedTypeIILabelCutoffReal_eq_zero_of_le_one {t : ℝ} (ht : t≤1) :
    markedTypeIILabelCutoffReal t=0 := by
  unfold markedTypeIILabelCutoffReal
  rw [spectralDyadicStep_zero ht,spectralDyadicStep_zero (by linarith : t/2≤1)]
  norm_num

theorem markedTypeIILabelCutoff_ratio_le_two : spectralDyadicRatio≤2 := by
  unfold spectralDyadicRatio
  exact Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩

theorem markedTypeIILabelCutoffReal_eq_zero_of_four_le {t : ℝ} (ht : 4≤t) :
    markedTypeIILabelCutoffReal t=0 := by
  unfold markedTypeIILabelCutoffReal
  rw [spectralDyadicStep_one (markedTypeIILabelCutoff_ratio_le_two.trans (by linarith)),
    spectralDyadicStep_one (markedTypeIILabelCutoff_ratio_le_two.trans (by linarith : 2≤t/2))]
  norm_num

theorem markedTypeIILabelCutoffReal_nonneg (t : ℝ) : 0≤markedTypeIILabelCutoffReal t := by
  by_cases h : t≤1
  · rw [markedTypeIILabelCutoffReal_eq_zero_of_le_one h]
  · exact sub_nonneg.mpr (spectralDyadicStep_monotone (by linarith))

theorem markedTypeIILabelCutoffReal_le_one (t : ℝ) : markedTypeIILabelCutoffReal t≤1 := by
  have h₁ := Real.smoothTransition.le_one ((t-1)/(spectralDyadicRatio-1))
  have h₂ := Real.smoothTransition.nonneg ((t/2-1)/(spectralDyadicRatio-1))
  unfold markedTypeIILabelCutoffReal spectralDyadicStep
  linarith

theorem markedTypeIILabelCutoff_norm_le_one (t : ℝ) : ‖markedTypeIILabelCutoff t‖≤1 := by
  unfold markedTypeIILabelCutoff
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (markedTypeIILabelCutoffReal_nonneg t)]
  exact markedTypeIILabelCutoffReal_le_one t

theorem markedTypeIILabelCutoff_support : Function.support markedTypeIILabelCutoff⊆Set.Icc 1 4 := by
  intro t ht
  change markedTypeIILabelCutoff t≠0 at ht
  constructor
  · by_contra! h
    exact ht (by simp only [markedTypeIILabelCutoff,markedTypeIILabelCutoffReal_eq_zero_of_le_one h.le,
      Complex.ofReal_zero])
  · by_contra! h
    exact ht (by simp only [markedTypeIILabelCutoff,markedTypeIILabelCutoffReal_eq_zero_of_four_le h.le,
      Complex.ofReal_zero])

theorem markedTypeIILabelCutoff_contDiff : ContDiff ℝ ∞ markedTypeIILabelCutoff := by
  have h : ContDiff ℝ ∞ markedTypeIILabelCutoffReal := by
    unfold markedTypeIILabelCutoffReal spectralDyadicStep
    fun_prop
  exact Complex.ofRealCLM.contDiff.comp h

theorem markedTypeIILabelCutoff_star (t : ℝ) : star (markedTypeIILabelCutoff t)=markedTypeIILabelCutoff t := by
  simp only [markedTypeIILabelCutoff,Complex.star_def,Complex.conj_ofReal]

theorem markedTypeIILabelCutoff_partial_sum (b : ℝ) (N : ℕ) :
    (∑ j∈Finset.range N,markedTypeIILabelCutoff (b/(2:ℝ)^j)) =
      (spectralDyadicStep b:ℂ)-(spectralDyadicStep (b/(2:ℝ)^N):ℂ) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    have hd : b/(2:ℝ)^(n+1)=(b/(2:ℝ)^n)/2 := by rw [pow_succ,div_div]
    rw [hd]
    unfold markedTypeIILabelCutoff markedTypeIILabelCutoffReal
    push_cast
    ring

theorem markedTypeIILabelCutoff_partition_range {b : ℝ} (N : ℕ) (hb : 2≤b) (hN : b≤(2:ℝ)^N) :
    (∑ j∈Finset.range N,markedTypeIILabelCutoff (b/(2:ℝ)^j))=1 := by
  rw [markedTypeIILabelCutoff_partial_sum,
    spectralDyadicStep_one (markedTypeIILabelCutoff_ratio_le_two.trans hb),
    spectralDyadicStep_zero ((div_le_one (by positivity : (0:ℝ)<2^N)).mpr hN)]
  norm_num

end
end ArtinMatthews
