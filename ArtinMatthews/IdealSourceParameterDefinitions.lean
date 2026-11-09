module

public import ArtinMatthews.IdealCharacterCellComparison
public import ArtinMatthews.IdealProbeDecay


set_option backward.privateInPublic true
@[expose] public section

/-! The source parameters are selected before the copied dimension.
The error budget retains the manuscript's log-three margin. -/
namespace ArtinMatthews
noncomputable section

def idealSourceErrorExponent (E C₀ : ℝ) (m : ℕ) : ℝ :=
  E+(m : ℝ)*C₀*Real.log 3+10

def idealSourceRationalExponent (E C₀ v₀ d : ℝ) (m : ℕ) : ℝ :=
  idealMinorBilinearExponent m C₀ v₀ d
    (idealComparisonPrecision d (idealSourceErrorExponent E C₀ m))

def idealSourceWidthExponent (E C₀ v₀ d C : ℝ) (m : ℕ) : ℝ :=
  idealComparisonWidth m C₀ v₀ d C
    (idealComparisonPrecision d (idealSourceErrorExponent E C₀ m))

def idealSourceThresholdExponent (E C₀ v₀ d C : ℝ) (m : ℕ) : ℝ :=
  idealComparisonThreshold m C₀ v₀ d C
    (idealComparisonPrecision d (idealSourceErrorExponent E C₀ m))

def idealSourceCostExponent (E C₀ v₀ d C : ℝ) (m : ℕ) : ℝ :=
  (m : ℝ)*C₀*Real.log 2+4*idealSourceRationalExponent E C₀ v₀ d m+
    2*idealSourceThresholdExponent E C₀ v₀ d C m+2

def idealSourceDimensionThreshold (m ell : ℕ) : ℕ :=
  max m ((m+ell)*(m+ell-1))

theorem idealSourceErrorExponent_nonneg {E C₀ : ℝ} (hE : 0 ≤ E) (hC₀ : 0 ≤ C₀) (m : ℕ) :
    0 ≤ idealSourceErrorExponent E C₀ m := by
  have hlog : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  unfold idealSourceErrorExponent
  positivity

theorem idealSourceErrorExponent_margin {E C₀ : ℝ} (hC₀ : 0 ≤ C₀) (m : ℕ) :
    E+((m : ℝ)*C₀)*Real.log 2+3 ≤ idealSourceErrorExponent E C₀ m := by
  have hlog : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
  have hm : 0 ≤ (m : ℝ)*C₀ := mul_nonneg (Nat.cast_nonneg _) hC₀
  have h := mul_le_mul_of_nonneg_left hlog hm
  unfold idealSourceErrorExponent
  linarith

theorem idealSourceParameters_nonnegative {E C₀ v₀ d C : ℝ}
    (hE : 0 ≤ E) (hC₀ : 0 ≤ C₀) (hd : 0 ≤ d) (hC : 0 ≤ C) (m : ℕ) :
    0 ≤ idealSourceErrorExponent E C₀ m ∧
    0 ≤ idealSourceRationalExponent E C₀ v₀ d m ∧
    1 ≤ idealSourceWidthExponent E C₀ v₀ d C m ∧
    0 ≤ idealSourceThresholdExponent E C₀ v₀ d C m ∧
    0 ≤ idealSourceCostExponent E C₀ v₀ d C m := by
  let A₀ := idealSourceErrorExponent E C₀ m
  let D := idealComparisonPrecision d A₀
  let a := idealSourceRationalExponent E C₀ v₀ d m
  let H := idealSourceWidthExponent E C₀ v₀ d C m
  let X := idealSourceThresholdExponent E C₀ v₀ d C m
  have hA : 0 ≤ A₀ := idealSourceErrorExponent_nonneg hE hC₀ m
  have hD : 0 ≤ D := by dsimp [D, idealComparisonPrecision]; linarith
  have hκ := idealGroupedBudgetExponent_nonneg m (v₀ := v₀) hC₀
  have ha : 0 ≤ a := by
    change 0 ≤ idealMinorCutoffExponent (D+2) (idealGroupedBudgetExponent m C₀ v₀) d
    unfold idealMinorCutoffExponent
    linarith
  have hH : 1 ≤ H := by
    change 1 ≤ idealComparisonWidth m C₀ v₀ d C D
    unfold idealComparisonWidth idealMajorBilinearWidth idealMajorCellExponent
    change 1 ≤ 4*a+a+C+(D+2)+4
    linarith
  have hX : 0 ≤ X := by
    change 0 ≤ idealDiscardedThresholdExponent d H D
    unfold idealDiscardedThresholdExponent
    linarith
  refine ⟨hA, ha, hH, hX, ?_⟩
  change 0 ≤ (m : ℝ)*C₀*Real.log 2+4*a+2*X+2
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  positivity

theorem idealSourceDimensionThreshold_spec (m ell J : ℕ)
    (hJ : idealSourceDimensionThreshold m ell ≤ J) :
    m ≤ J ∧ (m+ell)*(m+ell-1) ≤ J+ell := by
  have hm := (le_max_left m ((m+ell)*(m+ell-1))).trans hJ
  have hlarge := (le_max_right m ((m+ell)*(m+ell-1))).trans hJ
  exact ⟨hm, hlarge.trans (Nat.le_add_right J ell)⟩

end
end ArtinMatthews
