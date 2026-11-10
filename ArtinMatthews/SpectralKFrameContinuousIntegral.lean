module

public import ArtinMatthews.SpectralKFrameCompactProfiles
public import ArtinMatthews.SpectralKLMacdonaldBilinear
public import Mathlib.MeasureTheory.Order.Group.Lattice


set_option backward.privateInPublic true
@[expose] public section

/-! A compact K frame bounds a nonnegative spectral density on its
band. Its measured compact moments also recover measurability there. -/

noncomputable section
open Set MeasureTheory Filter OAI.CubicEisenstein
open scoped BigOperators
namespace ArtinMatthews

def spectralPrincipalBand (T : ℝ) : Set ℝ :=
  (fun t : ℝ => 1+|t|) ⁻¹' Icc T (2*T)

theorem spectralPrincipalBand_measurableSet (T : ℝ) : MeasurableSet (spectralPrincipalBand T) :=
  (measurableSet_Icc.preimage (by fun_prop))

theorem spectralCompactRealKTransform_continuous (F : ℝ → ℝ) (hF : Continuous F)
    (hcF : HasCompactSupport F) (hpF : tsupport F ⊆ Ioi (0 : ℝ)) :
    Continuous (spectralCompactRealKTransform F) := by
  let F₀ (x : ℝ) : ℂ := F x
  have hS : tsupport F₀ = tsupport F := by
    unfold tsupport
    congr 1
    ext x
    simp [F₀,Function.mem_support]
  have hF₀ : Continuous F₀ := Complex.continuous_ofReal.comp hF
  have hcF₀ : HasCompactSupport F₀ := by
    unfold HasCompactSupport
    rwa [hS]
  have hpF₀ : tsupport F₀ ⊆ Ioi (0 : ℝ) := hS ▸ hpF
  have hEq : spectralCompactRealKTransform F = spectralKLPhysicalAnalysisIntegral F₀ := by
    funext t
    rw [← spectralKLPhysicalAnalysisIntegral_measure F₀ hpF₀]
    unfold spectralCompactRealKTransform
    apply integral_congr_ae
    filter_upwards [spectralKLPositiveWeightMeasure_ae_pos (fun x => x⁻¹)] with x hx
    rw [schlafliBesselK_imaginary_eq_realKernel t hx,mul_comm]
  rw [hEq]
  exact spectralKLPhysicalAnalysisIntegral_continuous F₀ hF₀ hcF₀ hpF₀

theorem spectralKFrame_principal_integral_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) (A : ℝ → ℝ) (hA : ∀ t, 0 ≤ A t)
      (T V : ℝ), 1/2 ≤ T → 0 ≤ V →
      (∀ F : ℝ → ℝ, spectralKFrameProfileBound T F →
        Integrable (fun t => A t*‖spectralCompactRealKTransform F t‖^2) μ ∧
          (∫ t, A t*‖spectralCompactRealKTransform F t‖^2 ∂μ) ≤ V*spectralKFrameLength) →
      IntegrableOn (fun t => A t/Real.cosh (Real.pi*t)) (spectralPrincipalBand T) μ ∧
        (∫ t in spectralPrincipalBand T, A t/Real.cosh (Real.pi*t) ∂μ) ≤ C*T^2*V := by
  let L := spectralKFrameLength
  let P := Real.pi^2*L/5184
  have hL : 0 < L := spectralKFrameLength_pos
  have hP : 0 < P := by dsimp only [P]; positivity
  obtain ⟨C,hC,hFrame⟩ := spectralKFrame_exists_compact_phase_profiles
  refine ⟨2*C*L/P,by positivity,?_⟩
  intro μ A hA T V hhalf hV hMoment
  have hT : 0 < T := by linarith
  obtain ⟨modes,F,G,hcard,hProfiles,hLower⟩ := hFrame T hhalf
  let K (F₀ : ℝ → ℝ) (t : ℝ) := ‖spectralCompactRealKTransform F₀ t‖^2
  let Eₘ (m : ℤ) (t : ℝ) := A t*K (F m) t+A t*K (G m) t
  let E (t : ℝ) := ∑ m ∈ modes, Eₘ m t
  let D (t : ℝ) := ∑ m ∈ modes, (K (F m) t+K (G m) t)
  let B := spectralPrincipalBand T
  let f (t : ℝ) := A t/Real.cosh (Real.pi*t)
  have hB : MeasurableSet B := spectralPrincipalBand_measurableSet T
  have hEₘ (m : ℤ) : Integrable (Eₘ m) μ ∧ (∫ t, Eₘ m t ∂μ) ≤ 2*V*L := by
    obtain ⟨hF,hMF⟩ := hMoment (F m) (hProfiles m).1
    obtain ⟨hG,hMG⟩ := hMoment (G m) (hProfiles m).2
    refine ⟨hF.add hG,?_⟩
    dsimp only [Eₘ,K]
    rw [integral_add hF hG]
    exact (add_le_add hMF hMG).trans_eq (by dsimp only [L]; ring)
  have hE : Integrable E μ := integrable_finsetSum modes fun m _ => (hEₘ m).1
  have hE₀ (t : ℝ) : 0 ≤ E t := Finset.sum_nonneg fun _ _ => by
    exact add_nonneg (mul_nonneg (hA t) (sq_nonneg _)) (mul_nonneg (hA t) (sq_nonneg _))
  have hEq (t : ℝ) : E t = A t*D t := by
    simp only [E,Eₘ,D,Finset.mul_sum,mul_add]
  have hK (F₀ : ℝ → ℝ) (hF₀ : spectralKFrameProfileBound T F₀) :
      Continuous (K F₀) := by
    have h := spectralCompactRealKTransform_continuous F₀ hF₀.1.continuous hF₀.2.1
      (fun x hx => (by positivity : 0 < T/16).trans_le (hF₀.2.2.1 hx))
    exact h.norm.pow 2
  have hD : Continuous D := continuous_finsetSum modes (fun m _ =>
    (hK (F m) (hProfiles m).1).add (hK (G m) (hProfiles m).2))
  have hFrameLower (t : ℝ) (ht : t ∈ B) : P/(T*Real.cosh (Real.pi*t)) ≤ D t :=
    hLower t ht.1 ht.2
  have hDp (t : ℝ) (ht : t ∈ B) : 0 < D t :=
    (div_pos hP (mul_pos hT (Real.cosh_pos _))).trans_le (hFrameLower t ht)
  have hER : Integrable E (μ.restrict B) := hE.integrableOn
  have hDen : Measurable (fun t => D t*Real.cosh (Real.pi*t)) :=
    hD.measurable.mul (by fun_prop)
  have hfm : AEStronglyMeasurable f (μ.restrict B) := by
    apply (hER.aemeasurable.div hDen.aemeasurable).aestronglyMeasurable.congr
    filter_upwards [ae_restrict_mem hB] with t ht
    change E t/(D t*Real.cosh (Real.pi*t)) = A t/Real.cosh (Real.pi*t)
    rw [hEq]
    field_simp [(hDp t ht).ne',(Real.cosh_pos _).ne']
  have hf₀ (t : ℝ) : 0 ≤ f t := div_nonneg (hA t) (Real.cosh_pos _).le
  have hfMaj (t : ℝ) (ht : t ∈ B) : f t ≤ T/P*E t := by
    calc
      _ = T/P*(A t*(P/(T*Real.cosh (Real.pi*t)))) := by
        dsimp only [f]
        field_simp [hT.ne',hP.ne',(Real.cosh_pos _).ne']
      _ ≤ T/P*(A t*D t) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hFrameLower t ht) (hA t)) (div_nonneg hT.le hP.le)
      _ = _ := by rw [hEq]
  have hf : IntegrableOn f B μ := (hER.const_mul (T/P)).mono' hfm (by
    filter_upwards [ae_restrict_mem hB] with t ht
    exact (Real.norm_of_nonneg (hf₀ t)).symm ▸ hfMaj t ht)
  have hTotal : (∫ t, E t ∂μ) ≤ (C*T)*(2*V*L) := by
    dsimp only [E]
    rw [integral_finsetSum modes (fun m _ => (hEₘ m).1)]
    calc
      _ ≤ ∑ _m ∈ modes, 2*V*L := Finset.sum_le_sum (fun m _ => (hEₘ m).2)
      _ = (modes.card : ℝ)*(2*V*L) := by rw [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)
  refine ⟨hf,?_⟩
  change (∫ t in B, f t ∂μ) ≤ (2*C*L/P)*T^2*V
  calc
    _ ≤ ∫ t in B, T/P*E t ∂μ := integral_mono_ae hf (hER.const_mul (T/P))
      ((ae_restrict_mem hB).mono hfMaj)
    _ = (T/P)*(∫ t in B, E t ∂μ) := integral_const_mul _ _
    _ ≤ (T/P)*(∫ t, E t ∂μ) := mul_le_mul_of_nonneg_left
      (setIntegral_le_integral hE (ae_of_all _ hE₀)) (div_nonneg hT.le hP.le)
    _ ≤ (T/P)*((C*T)*(2*V*L)) := mul_le_mul_of_nonneg_left hTotal (div_nonneg hT.le hP.le)
    _ = _ := by ring

end ArtinMatthews
