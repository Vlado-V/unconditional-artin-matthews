module

public import ArtinMatthews.SpectralPeterssonUniform
public import ArtinMatthews.SpectralPeterssonFourierAtHeight


set_option backward.privateInPublic true
@[expose] public section

/-! The actual positive-row Fourier extraction commutes with the
Poincare series. Its uniform summable majorant is the original
Eisenstein vertical-strip estimate. -/

noncomputable section
open MeasureTheory Set UpperHalfPlane
open scoped MatrixGroups

namespace ArtinMatthews

theorem spectralPeterssonFourierAtHeight_tsum {ι : Type*} [Countable ι]
    (F : ι → UpperHalfPlane → ℂ) (n : ℕ+) (y : ℝ) (hy : 0 < y) (u : ι → ℝ)
    (hu : Summable u) (hcont : ∀ i, Continuous (F i))
    (hbound : ∀ i x, x ∈ Ioc (0 : ℝ) 1 → ‖F i (spectralPeterssonHeightPoint x y hy)‖ ≤ u i) :
    Summable (fun i => spectralPeterssonFourierAtHeight (F i) n y hy) ∧
      spectralPeterssonFourierAtHeight (fun z => ∑' i, F i z) n y hy =
        ∑' i, spectralPeterssonFourierAtHeight (F i) n y hy := by
  let μ := volume.restrict (Ioc (0 : ℝ) 1)
  let _ : IsFiniteMeasure μ := ⟨by simp [μ]⟩
  let z (x : ℝ) := spectralPeterssonHeightPoint x y hy
  let f (i : ι) (x : ℝ) := F i (z x)*spectralPeterssonFourierWeight n (z x)
  let W := Real.exp (2*Real.pi*(n : ℝ)*y)
  have hz : Continuous z := by
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    dsimp only [Function.comp_def,z]
    simp_rw [spectralPeterssonHeightPoint_coe]
    fun_prop
  have hW : Continuous (fun x => spectralPeterssonFourierWeight n (z x)) := by
    unfold spectralPeterssonFourierWeight
    exact Complex.continuous_exp.comp (by fun_prop)
  have hI (i : ι) : Integrable (f i) μ :=
    (((hcont i).comp hz).mul hW |>.integrableOn_Icc (μ := volume) (a := 0) (b := 1)).mono_set Ioc_subset_Icc_self
  have hM (i : ι) : (∫ x, ‖f i x‖ ∂μ) ≤ u i*W := by
    calc
      _ ≤ ∫ _ : ℝ, u i*W ∂μ := by
        apply integral_mono_ae (hI i).norm (integrable_const _)
        filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with x hx
        dsimp only [f]
        rw [norm_mul,spectralPeterssonFourierWeight_norm]
        exact mul_le_mul_of_nonneg_right (hbound i x hx) (Real.exp_nonneg _)
      _ = _ := by simp [μ]
  have hs : Summable (fun i => ∫ x, ‖f i x‖ ∂μ) :=
    Summable.of_nonneg_of_le (g := fun i => ∫ x, ‖f i x‖ ∂μ) (f := fun i => u i*W)
      (fun i => integral_nonneg (fun _ => norm_nonneg _)) hM (hu.mul_right W)
  refine ⟨(hasSum_integral_of_summable_integral_norm hI hs).summable, ?_⟩
  change (∫ x, (∑' i, F i (z x))*spectralPeterssonFourierWeight n (z x) ∂μ) =
    ∑' i, ∫ x, f i x ∂μ
  simp_rw [← tsum_mul_right]
  exact (integral_tsum_of_summable_integral_norm hI hs).symm

theorem gamma0PeterssonHorizontalRow_majorant (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k : ℕ) (hk : 3 ≤ k) (m : ℕ+) (y : ℝ) (hy : 0 < y) :
    ∃ u : Gamma0PeterssonPositiveRow N b a → ℝ, Summable u ∧
      ∀ p x, x ∈ Ioc (0 : ℝ) 1 →
        ‖gamma0PeterssonSignedSummand N b a k (m : ℕ) p.val (spectralPeterssonHeightPoint x y hy)‖ ≤ u p := by
  let w := (gamma0CuspTrueWidth N b : ℝ)
  have hw : 0 < w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N b)
  have hB : 0 < w*y := mul_pos hw hy
  let u (p : Gamma0PeterssonPositiveRow N b a) := gamma0PeterssonUniformRowBound N b a k w (w*y) hB p.val
  have hu : Summable u := (gamma0PeterssonUniformRowBound_summable N b a k hk w (w*y) hB).subtype
    {p | gamma0PeterssonRowPositive p}
  refine ⟨u,hu,?_⟩
  intro p x hx
  apply gamma0PeterssonSignedSummand_uniform_le
  unfold gamma0PeterssonWidthDilation verticalStrip
  simp only [mem_setOf_eq,cuspWidthDilation_re_smul,cuspWidthDilation_im_smul]
  change |w*x| ≤ w ∧ w*y ≤ w*y
  rw [abs_of_nonneg (mul_nonneg hw.le hx.1.le)]
  exact ⟨by simpa only [mul_one] using mul_le_mul_of_nonneg_left hx.2 hw.le,le_rfl⟩

theorem gamma0PeterssonFourierAtHeight_rows (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k : ℕ) (hk : 3 ≤ k) (m n : ℕ+) (y : ℝ) (hy : 0 < y) :
    let F (p : Gamma0PeterssonPositiveRow N b a) := gamma0PeterssonSignedSummand N b a k (m : ℕ) p.val
    Summable (fun p => spectralPeterssonFourierAtHeight (F p) n y hy) ∧
      spectralPeterssonFourierAtHeight (gamma0PeterssonPoincareChart N b a k (m : ℕ)) n y hy =
        ∑' p, spectralPeterssonFourierAtHeight (F p) n y hy := by
  let F (p : Gamma0PeterssonPositiveRow N b a) := gamma0PeterssonSignedSummand N b a k (m : ℕ) p.val
  let _ : Countable (Gamma0PeterssonSignedRow N b a) :=
    (show Function.Injective (fun p : Gamma0PeterssonSignedRow N b a => p.val) from
      Subtype.val_injective).countable
  let _ : Countable (Gamma0PeterssonPositiveRow N b a) :=
    (show Function.Injective (fun p : Gamma0PeterssonPositiveRow N b a => p.val) from
      Subtype.val_injective).countable
  obtain ⟨u,hu,hbound⟩ := gamma0PeterssonHorizontalRow_majorant N b a k hk m y hy
  exact spectralPeterssonFourierAtHeight_tsum F n y hy u hu
    (fun p => gamma0PeterssonSignedSummand_continuous N b a k (m : ℕ) p.val) hbound

end ArtinMatthews
