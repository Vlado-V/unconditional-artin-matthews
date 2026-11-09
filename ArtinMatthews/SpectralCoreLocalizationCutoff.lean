module

public import ArtinMatthews.SpectralCoreLocalization
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct


set_option backward.privateInPublic true
@[expose] public section

/-! Actual smooth rectangle cutoffs for spectral localization. -/

namespace ArtinMatthews
noncomputable section
open Set
open scoped Topology ContDiff

def spectralCoreHorizontalBump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def spectralCoreVerticalBump (Y : ℝ) (hY : 1 ≤ Y) : ContDiffBump (Y / 2 + 1 / 4) where
  rIn := Y / 2 - 1 / 4
  rOut := Y / 2
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

def spectralCoreCutoffFun (Y : ℝ) (hY : 1 ≤ Y) (p : ℝ × ℝ) : ℂ :=
  (spectralCoreHorizontalBump p.1 * spectralCoreVerticalBump Y hY p.2 : ℝ)

theorem spectralCoreCutoffFun_contDiff (Y : ℝ) (hY : 1 ≤ Y) :
    ContDiff ℝ ∞ (spectralCoreCutoffFun Y hY) :=
  Complex.ofRealCLM.contDiff.comp
    ((spectralCoreHorizontalBump.contDiff.comp contDiff_fst).mul
      ((spectralCoreVerticalBump Y hY).contDiff.comp contDiff_snd))

theorem spectralCoreCutoffFun_plateau (Y : ℝ) (hY : 1 ≤ Y)
    {p : ℝ × ℝ} (hp : p ∈ spectralPlaneRectangle (1 / 2) (1 / 2) Y) :
    spectralCoreCutoffFun Y hY p = 1 := by
  have hx : spectralCoreHorizontalBump p.1 = 1 := by
    apply spectralCoreHorizontalBump.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq]
    change |p.1 - 0| ≤ 1 / 2
    rw [sub_zero, abs_le]
    exact hp.1
  have hy : spectralCoreVerticalBump Y hY p.2 = 1 := by
    apply (spectralCoreVerticalBump Y hY).one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq]
    change |p.2 - (Y / 2 + 1 / 4)| ≤ Y / 2 - 1 / 4
    exact abs_le.mpr ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩
  simp only [spectralCoreCutoffFun, hx, hy, mul_one, Complex.ofReal_one]

theorem spectralCoreCutoffFun_support (Y : ℝ) (hY : 1 ≤ Y) :
    Function.support (spectralCoreCutoffFun Y hY) ⊆
      spectralPlaneRectangle 1 (1 / 4) (Y + 1) := by
  intro p hp
  change ((spectralCoreHorizontalBump p.1 * spectralCoreVerticalBump Y hY p.2 : ℝ) : ℂ) ≠ 0 at hp
  have hprod := mul_ne_zero_iff.mp (Complex.ofReal_ne_zero.mp hp)
  have hx : p.1 ∈ Metric.ball (0 : ℝ) 1 := by
    change p.1 ∈ Metric.ball (0 : ℝ) spectralCoreHorizontalBump.rOut
    rw [← spectralCoreHorizontalBump.support_eq]
    exact hprod.1
  have hy : p.2 ∈ Metric.ball (Y / 2 + 1 / 4) (Y / 2) := by
    change p.2 ∈ Metric.ball (Y / 2 + 1 / 4) (spectralCoreVerticalBump Y hY).rOut
    rw [← (spectralCoreVerticalBump Y hY).support_eq]
    exact hprod.2
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt] at hx
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hy
  exact ⟨⟨hx.1.le, hx.2.le⟩, ⟨by linarith [hy.1], by linarith [hy.2]⟩⟩

theorem spectralCoreCutoffFun_tsupport (Y : ℝ) (hY : 1 ≤ Y) :
    tsupport (spectralCoreCutoffFun Y hY) ⊆ spectralPlaneRectangle 1 (1 / 4) (Y + 1) :=
  closure_minimal (spectralCoreCutoffFun_support Y hY)
    (spectralPlaneRectangle_compact 1 (1 / 4) (Y + 1)).isClosed

theorem spectralCoreCutoffFun_hasCompactSupport (Y : ℝ) (hY : 1 ≤ Y) :
    HasCompactSupport (spectralCoreCutoffFun Y hY) :=
  (spectralPlaneRectangle_compact 1 (1 / 4) (Y + 1)).of_isClosed_subset
    (isClosed_tsupport _) (spectralCoreCutoffFun_tsupport Y hY)

/-- The literal smooth product cutoff, as a Schwartz function on the plane. -/
def spectralCoreCutoff (Y : ℝ) (hY : 1 ≤ Y) : SchwartzMap (ℝ × ℝ) ℂ :=
  (spectralCoreCutoffFun_hasCompactSupport Y hY).toSchwartzMap
    (spectralCoreCutoffFun_contDiff Y hY)

theorem spectralCoreCutoff_apply (Y : ℝ) (hY : 1 ≤ Y) (p : ℝ × ℝ) :
    spectralCoreCutoff Y hY p =
      (spectralCoreHorizontalBump p.1 * spectralCoreVerticalBump Y hY p.2 : ℝ) := rfl

theorem spectralCoreCutoff_plateau (Y : ℝ) (hY : 1 ≤ Y)
    {p : ℝ × ℝ} (hp : p ∈ spectralPlaneRectangle (1 / 2) (1 / 2) Y) :
    spectralCoreCutoff Y hY p = 1 := spectralCoreCutoffFun_plateau Y hY hp

theorem spectralCoreCutoff_support (Y : ℝ) (hY : 1 ≤ Y) :
    tsupport (spectralCoreCutoff Y hY) ⊆ spectralPlaneRectangle 1 (1 / 4) (Y + 1) :=
  spectralCoreCutoffFun_tsupport Y hY

theorem spectralCoreCutoff_re_nonneg (Y : ℝ) (hY : 1 ≤ Y) (p : ℝ × ℝ) :
    0 ≤ (spectralCoreCutoff Y hY p).re := by
  rw [spectralCoreCutoff_apply, Complex.ofReal_re]
  exact mul_nonneg spectralCoreHorizontalBump.nonneg (spectralCoreVerticalBump Y hY).nonneg

theorem spectralCoreCutoff_norm_le_one (Y : ℝ) (hY : 1 ≤ Y) (p : ℝ × ℝ) :
    ‖spectralCoreCutoff Y hY p‖ ≤ 1 := by
  rw [spectralCoreCutoff_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg spectralCoreHorizontalBump.nonneg
      (spectralCoreVerticalBump Y hY).nonneg)]
  calc
    _ ≤ 1 * spectralCoreVerticalBump Y hY p.2 :=
      mul_le_mul_of_nonneg_right spectralCoreHorizontalBump.le_one
        (spectralCoreVerticalBump Y hY).nonneg
    _ ≤ 1 := by simpa only [one_mul] using (spectralCoreVerticalBump Y hY).le_one (x := p.2)

theorem exists_spectralCoreLocalizationCutoff (Y : ℝ) (hY : 1 ≤ Y) :
    ∃ φ : SchwartzMap (ℝ × ℝ) ℂ,
      (∀ p ∈ spectralPlaneRectangle (1 / 2) (1 / 2) Y, φ p = 1) ∧
      tsupport φ ⊆ spectralPlaneRectangle 1 (1 / 4) (Y + 1) ∧
      ∀ p, ‖φ p‖ ≤ 1 :=
  ⟨spectralCoreCutoff Y hY, fun _ hp => spectralCoreCutoff_plateau Y hY hp,
    spectralCoreCutoff_support Y hY, spectralCoreCutoff_norm_le_one Y hY⟩

end
end ArtinMatthews
