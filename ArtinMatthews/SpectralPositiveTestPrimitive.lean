module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! A zero-mean compact smooth positive-half-line test has a literal compact primitive.
Compactness of the primitive is proved from the support bounds and the zero total integral. -/
namespace ArtinMatthews
open Set Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section

/-- Every compact positive test support is enclosed strictly between positive endpoints,
with the reference point `1` also strictly inside the interval. -/
theorem spectralPositiveTest_support_enclosure (σ : ℝ → ℝ)
    (hcompact : HasCompactSupport σ) (hsupport : tsupport σ ⊆ Ioi 0) :
    ∃ a b : ℝ, 0 < a ∧ a < 1 ∧ 1 < b ∧ tsupport σ ⊆ Ioo a b := by
  by_cases hne : (tsupport σ).Nonempty
  · obtain ⟨c, hc⟩ := hcompact.exists_isLeast hne
    obtain ⟨d, hd⟩ := hcompact.exists_isGreatest hne
    have hcpos : 0 < c := hsupport hc.1
    refine ⟨min c 1 / 2, max d 1 + 1, ?_, ?_, ?_, ?_⟩
    · exact div_pos (lt_min hcpos zero_lt_one) (by norm_num)
    · have := min_le_right c 1
      linarith
    · have := le_max_right d 1
      linarith
    · intro x hx
      have hcx := hc.2 hx
      have hxd := hd.2 hx
      have hmin := min_le_left c 1
      have hmax := le_max_left d 1
      have hmpos : 0 < min c 1 := lt_min hcpos zero_lt_one
      constructor <;> linarith
  · refine ⟨1 / 2, 2, by norm_num, by norm_num, by norm_num, ?_⟩
    exact fun x hx => (hne ⟨x, hx⟩).elim

/-- The chosen primitive, based at zero. -/
def spectralPositiveTestPrimitive (σ : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ t in 0..y, σ t

/-- Fundamental theorem of calculus for the actual chosen primitive. -/
theorem spectralPositiveTestPrimitive_deriv {σ : ℝ → ℝ} (hσ : Continuous σ) :
    deriv (spectralPositiveTestPrimitive σ) = σ := by
  funext y
  exact hσ.deriv_integral σ 0 y

/-- Smoothness is derived from the actual derivative identity. -/
theorem spectralPositiveTestPrimitive_contDiff {σ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ) :
    ContDiff ℝ ∞ (spectralPositiveTestPrimitive σ) := by
  apply contDiff_infty_iff_deriv.mpr
  constructor
  · intro y
    exact (hσ.continuous.integral_hasStrictDerivAt 0 y).hasDerivAt.differentiableAt
  · rw [spectralPositiveTestPrimitive_deriv hσ.continuous]
    exact hσ

/-- The primitive vanishes before a positive lower bound for the original support. -/
theorem spectralPositiveTestPrimitive_zero_left {σ : ℝ → ℝ} {a b y : ℝ}
    (ha : 0 < a) (hsupport : tsupport σ ⊆ Ioo a b) (hy : y ≤ a) :
    spectralPositiveTestPrimitive σ y = 0 := by
  unfold spectralPositiveTestPrimitive
  apply intervalIntegral.integral_zero_ae
  apply Eventually.of_forall
  intro x hx
  have hxa : x ≤ a := hx.2.trans (max_le ha.le hy)
  exact image_eq_zero_of_notMem_tsupport (fun ht => (hsupport ht).1.not_ge hxa)

/-- Past the upper support bound the primitive is the zero total integral. -/
theorem spectralPositiveTestPrimitive_zero_right {σ : ℝ → ℝ} {a b y : ℝ}
    (ha : 0 < a) (hsupport : tsupport σ ⊆ Ioo a b) (hmean : ∫ t, σ t = 0)
    (hy : b ≤ y) : spectralPositiveTestPrimitive σ y = 0 := by
  unfold spectralPositiveTestPrimitive
  rw [intervalIntegral.integral_eq_integral_of_support_subset, hmean]
  intro x hx
  have ht := hsupport (subset_tsupport σ hx)
  exact ⟨ha.trans ht.1, ht.2.le.trans hy⟩

/-- Both tail vanishings give a proved compact enclosure of the primitive support. -/
theorem spectralPositiveTestPrimitive_tsupport {σ : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hsupport : tsupport σ ⊆ Ioo a b) (hmean : ∫ t, σ t = 0) :
    tsupport (spectralPositiveTestPrimitive σ) ⊆ Icc a b := by
  apply closure_minimal _ isClosed_Icc
  intro y hy
  have hn : spectralPositiveTestPrimitive σ y ≠ 0 := hy
  constructor
  · by_contra h
    exact hn (spectralPositiveTestPrimitive_zero_left ha hsupport (le_of_not_ge h))
  · by_contra h
    exact hn (spectralPositiveTestPrimitive_zero_right ha hsupport hmean (le_of_not_ge h))

/-- The literal primitive is smooth, compactly supported away from zero, and differentiates to
exactly the given test. No compact-support hypothesis on the primitive is assumed. -/
theorem spectralPositiveTestPrimitive_properties (σ : ℝ → ℝ) (hσ : ContDiff ℝ ∞ σ)
    (hcompact : HasCompactSupport σ) (hsupport : tsupport σ ⊆ Ioi 0)
    (hmean : ∫ t, σ t = 0) :
    ContDiff ℝ ∞ (spectralPositiveTestPrimitive σ) ∧
      HasCompactSupport (spectralPositiveTestPrimitive σ) ∧
      tsupport (spectralPositiveTestPrimitive σ) ⊆ Ioi 0 ∧
      deriv (spectralPositiveTestPrimitive σ) = σ := by
  obtain ⟨a, b, ha, _, _, hs⟩ := spectralPositiveTest_support_enclosure σ hcompact hsupport
  have hp := spectralPositiveTestPrimitive_tsupport ha hs hmean
  exact ⟨spectralPositiveTestPrimitive_contDiff hσ,
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hp,
    fun _ hx => ha.trans_le (hp hx).1,
    spectralPositiveTestPrimitive_deriv hσ.continuous⟩

/-- A compact primitive within the positive half-line for every smooth zero-mean test. -/
theorem spectralPositiveTestPrimitive_exists (σ : ℝ → ℝ) (hσ : ContDiff ℝ ∞ σ)
    (hcompact : HasCompactSupport σ) (hsupport : tsupport σ ⊆ Ioi 0)
    (hmean : ∫ t, σ t = 0) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧
      tsupport ρ ⊆ Ioi 0 ∧ deriv ρ = σ :=
  ⟨spectralPositiveTestPrimitive σ,
    spectralPositiveTestPrimitive_properties σ hσ hcompact hsupport hmean⟩

end
end ArtinMatthews
