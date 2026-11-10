module

public import ArtinMatthews.MarkedMinorArcTrivial
public import ArtinMatthews.MarkedMinorArcCutoff
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional


set_option backward.privateInPublic true
@[expose] public section

/-! The actual smooth determinant matrix is a Bochner integral of the actual
shifted exponential matrices, in their genuine L² operator norm. -/
namespace ArtinMatthews
open Matrix MeasureTheory
open scoped BigOperators FourierTransform Matrix.Norms.L2Operator

/-- The actual spatial cutoff in the clean determinant Fourier fiber. -/
noncomputable def markedMinorSmoothDeterminantMatrix (ψ : SchwartzMap ℝ ℂ)
    (L T : ℤ) (M N : ℕ) (Y θ : ℝ) :
    Matrix (MarkedMinorBoxIndex L T M N) (MarkedMinorBoxIndex L T M N) ℂ :=
  fun h l => ((Y : ℂ)⁻¹) *
    (ψ (((h.1.1 : ℝ)*l.1.2-(h.1.2 : ℝ)*l.1.1)/Y) *
      OAI.Problem337.RealPhase.phase (θ*((h.1.1 : ℝ)*l.1.2-(h.1.2 : ℝ)*l.1.1)))

private noncomputable def minorMatrixEntry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) : Matrix ι ι ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A : Matrix ι ι ℂ => A i j
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

private theorem minorMatrixEntry_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (A : Matrix ι ι ℂ) : minorMatrixEntry i j A = A i j := rfl

private theorem minorMatrix_norm_integral_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ℝ → Matrix ι ι ℂ) :
    ‖∫ u : ℝ, F u‖ ≤ ∫ u : ℝ, ‖F u‖ :=
  norm_integral_le_integral_norm F

/-- Shifted determinant matrices vary continuously in their real frequency. -/
theorem markedMinorDeterminantMatrix_continuous (L T : ℤ) (M N : ℕ) (Y θ : ℝ) :
    Continuous (fun u : ℝ => markedMinorDeterminantMatrix L T M N Y (θ+u/Y)) := by
  apply continuous_pi
  intro h
  apply continuous_pi
  intro l
  unfold markedMinorDeterminantMatrix OAI.Problem337.RealPhase.phase
  fun_prop

/-- The actual Fourier matrix integral converges absolutely in operator norm. -/
theorem markedMinorCutoffMatrix_integrable (ψ : SchwartzMap ℝ ℂ)
    (L T : ℤ) (M N : ℕ) {Y : ℝ} (hY : 0 < Y) (θ : ℝ) :
    Integrable (fun u : ℝ => (𝓕 ψ) u • markedMinorDeterminantMatrix L T M N Y (θ+u/Y)) := by
  have hmajor : Integrable (fun u : ℝ => ‖(𝓕 ψ) u‖*(((M : ℝ)*(N : ℝ))/Y)) :=
    (show Integrable (fun u : ℝ => ‖(𝓕 ψ) u‖) from (𝓕 ψ).integrable.norm).mul_const _
  have hcont : Continuous (fun u : ℝ => (𝓕 ψ) u • markedMinorDeterminantMatrix L T M N Y (θ+u/Y)) :=
    (𝓕 ψ).continuous.smul (markedMinorDeterminantMatrix_continuous L T M N Y θ)
  apply hmajor.mono' hcont.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun u => by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left
      (markedMinorDeterminantMatrix_norm_le_area L T M N hY (θ+u/Y)) (norm_nonneg _))

/-- Fourier inversion of the actual cutoff holds as an operator-valued
integral, retaining the determinant scale and the full shifted frequency. -/
theorem markedMinorSmoothDeterminantMatrix_eq_integral (ψ : SchwartzMap ℝ ℂ)
    (L T : ℤ) (M N : ℕ) {Y : ℝ} (hY : 0 < Y) (θ : ℝ) :
    markedMinorSmoothDeterminantMatrix ψ L T M N Y θ =
      ∫ u : ℝ, (𝓕 ψ) u • markedMinorDeterminantMatrix L T M N Y (θ+u/Y) := by
  classical
  have hint := markedMinorCutoffMatrix_integrable ψ L T M N hY θ
  ext h l
  have he := ((minorMatrixEntry h l).integral_comp_comm hint).symm
  simp only [minorMatrixEntry_apply] at he
  rw [he]
  change ((Y : ℂ)⁻¹) *
      (ψ (((h.1.1 : ℝ)*l.1.2-(h.1.2 : ℝ)*l.1.1)/Y) *
        OAI.Problem337.RealPhase.phase (θ*((h.1.1 : ℝ)*l.1.2-(h.1.2 : ℝ)*l.1.1))) =
      ∫ u : ℝ, (𝓕 ψ) u * (((Y : ℂ)⁻¹) * OAI.Problem337.RealPhase.phase
        ((θ+u/Y)*((h.1.1 : ℝ)*l.1.2-(h.1.2 : ℝ)*l.1.1)))
  rw [marked_minor_cutoff_fourier]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun u => by ring)

/-- Triangle inequality for the genuine operator Fourier integral. -/
theorem markedMinorSmoothDeterminantMatrix_norm_le_integral (ψ : SchwartzMap ℝ ℂ)
    (L T : ℤ) (M N : ℕ) {Y : ℝ} (hY : 0 < Y) (θ : ℝ) :
    ‖markedMinorSmoothDeterminantMatrix ψ L T M N Y θ‖ ≤
      ∫ u : ℝ, ‖(𝓕 ψ) u‖ * ‖markedMinorDeterminantMatrix L T M N Y (θ+u/Y)‖ := by
  rw [markedMinorSmoothDeterminantMatrix_eq_integral ψ L T M N hY θ]
  have hh := minorMatrix_norm_integral_le
    (fun u : ℝ => (𝓕 ψ) u • markedMinorDeterminantMatrix L T M N Y (θ+u/Y))
  simpa only [norm_smul] using hh


set_option maxHeartbeats 1200000 in
/-- The actual smooth determinant Fourier fiber has every logarithmic
operator-norm saving. The major-arc exponent `G+3` depends only on G;
the fixed Schwartz cutoff and geometry constants affect only the threshold. -/
theorem marked_minor_smooth_determinant_opNorm (ψ : SchwartzMap ℝ ℂ) {G C H : ℝ}
    (hG : 0 < G) (hC : 1 ≤ C) (hH : 1 ≤ H) :
    ∀ᶠ Λ : ℝ in Filter.atTop, ∀ (Y : ℝ) (L T : ℤ) (M N : ℕ) (θ : ℝ),
      Real.exp (Λ^(1/10 : ℝ)) ≤ Y → Y ≤ Real.exp (H*Λ^(1/5 : ℝ)) →
      1 ≤ M → 1 ≤ N → (M : ℝ)*(N : ℝ) ≤ C*Y →
      (M : ℝ) ≤ C*Y^(9/10 : ℝ) → (N : ℝ) ≤ C*Y^(9/10 : ℝ) →
      ¬MarkedInMajorArcs θ (Λ^(G+3)) Y →
      ‖markedMinorSmoothDeterminantMatrix ψ L T M N Y θ‖ ≤ Λ^(-G) := by
  let I₀ := markedMinorCutoffMoment ψ 0
  let I₁ := markedMinorCutoffMoment ψ 1
  have h₁ := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1)).const_mul I₀
  have h₃ := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<3)).const_mul (2*C*I₁)
  have hlim : Filter.Tendsto (fun Λ : ℝ => I₀*Λ^(-1 : ℝ)+(2*C*I₁)*Λ^(-3 : ℝ))
      Filter.atTop (nhds 0) := by simpa only [mul_zero,add_zero] using h₁.add h₃
  have hsmall := hlim.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))
  have hbare := marked_minor_clean_determinant_opNorm (show 0<G+1 by linarith) hC hH
  simp only [show (G+1)+2 = G+3 by ring] at hbare
  filter_upwards [hbare,hsmall,Filter.eventually_ge_atTop (1:ℝ)] with Λ hx hsmall hΛ
  intro Y L T M N θ hYlo hYhi hMpos hNpos hMN hM hN hminor
  have hΛp : 0 < Λ := by linarith
  have hYp : 0 < Y := (Real.exp_pos _).trans_le hYlo
  let R := Λ^(G+3)/2
  let S : Set ℝ := {u | ‖u‖ ≤ R}
  have hR : 0 < R := by dsimp [R]; positivity
  have hS : MeasurableSet S := measurableSet_le measurable_norm measurable_const
  have hf : Integrable (fun u : ℝ => ‖(𝓕 ψ) u‖) := (𝓕 ψ).integrable.norm
  have hi : Integrable (fun u : ℝ => ‖(𝓕 ψ) u‖ *
      ‖markedMinorDeterminantMatrix L T M N Y (θ+u/Y)‖) := by
    simpa only [norm_smul] using (markedMinorCutoffMatrix_integrable ψ L T M N hYp θ).norm
  have hb (u : ℝ) (hu : u ∈ S) :
      ‖markedMinorDeterminantMatrix L T M N Y (θ+u/Y)‖ ≤ Λ^(-(G+1)) := by
    exact hx Y L T M N θ u hYlo hYhi hMpos hNpos hMN hM hN hminor
      (by simpa only [S,R,Set.mem_ofPred_eq,Real.norm_eq_abs] using hu)
  have hI₀ : (∫ u : ℝ in S, ‖(𝓕 ψ) u‖) ≤ I₀ := by
    have hh := setIntegral_le_integral (s := S) hf
      (Filter.Eventually.of_forall (fun u => norm_nonneg ((𝓕 ψ) u)))
    simpa only [I₀,markedMinorCutoffMoment,pow_zero,one_mul] using hh
  have hI₁ : (∫ u : ℝ in Sᶜ, ‖(𝓕 ψ) u‖) ≤ R⁻¹*I₁ := by
    simpa only [S,Set.compl_ofPred,not_le,pow_one,I₁] using marked_minor_cutoff_tail ψ 1 hR
  have hnear : (∫ u : ℝ in S, ‖(𝓕 ψ) u‖ *
      ‖markedMinorDeterminantMatrix L T M N Y (θ+u/Y)‖) ≤ I₀*Λ^(-(G+1)) := by
    calc
      _ ≤ ∫ u : ℝ in S, ‖(𝓕 ψ) u‖*Λ^(-(G+1)) :=
        setIntegral_mono_on hi.integrableOn (hf.mul_const _).integrableOn hS
          (fun u hu => mul_le_mul_of_nonneg_left (hb u hu) (norm_nonneg _))
      _ = (∫ u : ℝ in S, ‖(𝓕 ψ) u‖)*Λ^(-(G+1)) := integral_mul_const _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hI₀ (Real.rpow_nonneg hΛp.le _)
  have hfar : (∫ u : ℝ in Sᶜ, ‖(𝓕 ψ) u‖ *
      ‖markedMinorDeterminantMatrix L T M N Y (θ+u/Y)‖) ≤ (R⁻¹*I₁)*C := by
    calc
      _ ≤ ∫ u : ℝ in Sᶜ, ‖(𝓕 ψ) u‖*C :=
        setIntegral_mono_on hi.integrableOn (hf.mul_const _).integrableOn hS.compl
          (fun u _ => mul_le_mul_of_nonneg_left
            (markedMinorDeterminantMatrix_norm_le L T M N hYp hMN (θ+u/Y)) (norm_nonneg _))
      _ = (∫ u : ℝ in Sᶜ, ‖(𝓕 ψ) u‖)*C := integral_mul_const _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hI₁ (by linarith)
  have hmain : ‖markedMinorSmoothDeterminantMatrix ψ L T M N Y θ‖ ≤
      I₀*Λ^(-(G+1))+(R⁻¹*I₁)*C := by
    apply le_trans (markedMinorSmoothDeterminantMatrix_norm_le_integral ψ L T M N hYp θ)
    rw [← integral_add_compl hS hi]
    exact add_le_add hnear hfar
  have hRpow : R⁻¹ = 2*Λ^(-(G+3)) := by
    dsimp [R]
    rw [inv_div,div_eq_mul_inv,← Real.rpow_neg hΛp.le]
  have hp₁ : Λ^(-(G+1)) = Λ^(-G)*Λ^(-1 : ℝ) := by
    rw [← Real.rpow_add hΛp]
    congr 1
    ring
  have hp₃ : Λ^(-(G+3)) = Λ^(-G)*Λ^(-3 : ℝ) := by
    rw [← Real.rpow_add hΛp]
    congr 1
    ring
  rw [hRpow,hp₁,hp₃] at hmain
  calc
    _ ≤ I₀*(Λ^(-G)*Λ^(-1 : ℝ))+(2*(Λ^(-G)*Λ^(-3 : ℝ))*I₁)*C := hmain
    _ = Λ^(-G)*(I₀*Λ^(-1 : ℝ)+(2*C*I₁)*Λ^(-3 : ℝ)) := by ring
    _ ≤ Λ^(-G)*1 := mul_le_mul_of_nonneg_left hsmall.le (Real.rpow_nonneg hΛp.le _)
    _ = _ := mul_one _

end ArtinMatthews
