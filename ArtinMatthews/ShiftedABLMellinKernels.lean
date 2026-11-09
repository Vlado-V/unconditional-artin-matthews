module

public import ArtinMatthews.ShiftedABLSourceSmoothness
public import ArtinMatthews.SpectralDyadicPartition
public import ArtinMatthews.ShiftedConvolutionLogPhase


set_option backward.privateInPublic true
@[expose] public section

/-! Exact log separation in the two variables used by the actual dual
blocks. The dual windows are the original interlaced smooth windows and
the modulus window is a fixed plateau on the whole circle family. -/

noncomputable section
open Complex MeasureTheory Set OAI
open scoped ContDiff BigOperators

namespace ArtinMatthews

private def shiftedABLMellinWindow (i : Fin 2) (u : ℝ) : ℂ :=
  if i = 0 then
    ((spectralDyadicWeight (Real.exp u) +
      spectralDyadicWeight (spectralDyadicRatio*Real.exp u) : ℝ) : ℂ)
  else shiftedSourcePlateau (Real.exp u)

private def shiftedABLMellinExponent (i : Fin 2) : ℝ := if i = 0 then 1 else -2

private theorem shiftedABLMellinWindow_support (i : Fin 2) (u : ℝ)
    (hu : shiftedABLMellinWindow i u ≠ 0) : |u| ≤ Real.log 3 := by
  have hRatio := spectralDyadicRatio_one_lt
  have hRatio2 : spectralDyadicRatio ≤ 2 := by
    nlinarith [spectralDyadicRatio_sq, sq_nonneg (spectralDyadicRatio-1)]
  have hExp : (1/2 : ℝ) ≤ Real.exp u ∧ Real.exp u ≤ 5/2 := by
    by_cases hi : i = 0
    · simp only [shiftedABLMellinWindow,hi,ite_true,ne_eq,Complex.ofReal_eq_zero] at hu
      by_cases hw : spectralDyadicWeight (Real.exp u) = 0
      · have hw' : spectralDyadicWeight (spectralDyadicRatio*Real.exp u) ≠ 0 := by
          simpa only [hw,zero_add] using hu
        obtain ⟨hl,hh⟩ := spectralDyadicWeight_support hw'
        have he0 := (Real.exp_pos u).le
        have h₂ := mul_le_mul_of_nonneg_right hRatio2 he0
        have h₁ := mul_le_mul_of_nonneg_right hRatio.le he0
        exact ⟨by linarith, by linarith⟩
      · obtain ⟨hl,hh⟩ := spectralDyadicWeight_support hw
        exact ⟨by linarith, by linarith⟩
    · apply shiftedSourcePlateau_support
      change shiftedSourcePlateau (Real.exp u) ≠ 0
      simpa only [shiftedABLMellinWindow,hi,ite_false] using hu
  have hlog : Real.exp (Real.log 3) = (3 : ℝ) := Real.exp_log (by norm_num)
  apply abs_le.mpr
  constructor
  · apply Real.exp_le_exp.mp
    rw [Real.exp_neg,hlog]
    linarith [hExp.1]
  · apply Real.exp_le_exp.mp
    rw [hlog]
    linarith [hExp.2]

/-- The original dual window with its log-Fourier phase at a normalized
positive dual index. -/
def shiftedABLMellinDualPhase (j k : ℕ) (t : ℝ) : ℂ :=
  (spectralDyadicBlock j k : ℂ) *
    FourierBridge.logPhase t (Real.log ((k : ℝ)/(2 : ℝ)^j))

/-- The modulus dependence of the log-separated kernel. -/
def shiftedABLMellinCirclePhase (Q : ℝ) (t q : ℝ) : ℂ :=
  FourierBridge.logPhase t (-2*Real.log (q/Q))

private theorem shiftedABLMellinKernel_identity
    (F : ℝ → ℂ) (b : SchwartzMap ℝ ℂ) (j : ℕ) {Q : ℝ} (hQ : 0 < Q)
    (hsep : ∀ y : Fin 2 → ℝ,
      (∏ i, shiftedABLMellinWindow i (y i)) *
        F (((2 : ℝ)^j/Q^2)*Real.exp (∑ i, shiftedABLMellinExponent i*y i)) =
          ∫ t : ℝ, (∏ i, shiftedABLMellinWindow i (y i) *
            FourierBridge.logPhase t (shiftedABLMellinExponent i*y i))*b t)
    (k : ℕ) (hk : 0 < k) (q : ℝ) (hql : Q ≤ q) (hqu : q ≤ 2*Q) :
    (spectralDyadicBlock j k : ℂ)*F ((k : ℝ)/q^2) =
      ∫ t : ℝ, shiftedABLMellinDualPhase j k t * shiftedABLMellinCirclePhase Q t q * b t := by
  let K : ℝ := 2^j
  have hK : 0 < K := by positivity
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hq : 0 < q := hQ.trans_le hql
  let y (i : Fin 2) := if i = 0 then Real.log ((k : ℝ)/K) else Real.log (q/Q)
  have hi : (1 : Fin 2) ≠ 0 := by decide
  have hy0 : y 0 = Real.log ((k : ℝ)/K) := by simp [y]
  have hy1 : y 1 = Real.log (q/Q) := by simp [y,hi]
  have hV0 : shiftedABLMellinWindow 0 (y 0) = (spectralDyadicBlock j k : ℂ) := by
    simp only [hy0,shiftedABLMellinWindow,eq_self_iff_true,ite_true,
      Real.exp_log (div_pos hk' hK),spectralDyadicBlock,mul_div_assoc,K]
  have hV1 : shiftedABLMellinWindow 1 (y 1) = 1 := by
    simp only [hy1,shiftedABLMellinWindow,hi,ite_false,Real.exp_log (div_pos hq hQ)]
    exact shiftedSourcePlateau_one _ ⟨(le_div_iff₀ hQ).2 (by simpa using hql),
      (div_le_iff₀ hQ).2 hqu⟩
  have harg : K/Q^2 * Real.exp (Real.log ((k : ℝ)/K)+(-2)*Real.log (q/Q)) = (k : ℝ)/q^2 := by
    rw [show Real.log ((k : ℝ)/K)+(-2)*Real.log (q/Q) =
        Real.log ((k : ℝ)/K) - Real.log ((q/Q)^2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_sub,Real.exp_log (div_pos hk' hK),Real.exp_log (sq_pos_of_pos (div_pos hq hQ))]
    field_simp [hK.ne',hq.ne',hQ.ne'] <;> ring
  have h := hsep y
  simp only [Fin.prod_univ_two,Fin.sum_univ_two,hV0,hV1] at h
  simp only [shiftedABLMellinExponent,eq_self_iff_true,ite_true,hi,ite_false,
    hy0,hy1,one_mul,mul_one] at h
  change (spectralDyadicBlock j k : ℂ)*F
      (K/Q^2 * Real.exp (Real.log ((k : ℝ)/K)+(-2)*Real.log (q/Q))) = _ at h
  rw [harg] at h
  exact h

/-- The two actual weighted Bessel transforms admit separated kernels
with constants chosen before all varying source and dual scales. -/
theorem shiftedABLSource_mellin_kernels (A J : ℕ)
    (Cg : ℕ → ℝ) (hCg : ∀ j, 0 ≤ Cg j) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : ℝ → ℂ), ContDiff ℝ ∞ g →
      ∀ (T m1 m2 : ℝ), 0 < T → 0 < m1 → 0 < m2 →
        Function.support g ⊆ Icc T (2*T) → 1 ≤ m1*T → 1 ≤ m2*T →
        (∀ j x, ‖iteratedDeriv j g x‖ ≤ Cg j/T^j) →
        ∀ (Q : ℝ), 0 < Q → ∀ (j1 j2 : ℕ), ∃ b1 b2 : SchwartzMap ℝ ℂ,
          (∀ (k : ℕ), 0 < k → ∀ (q : ℝ), Q ≤ q → q ≤ 2*Q →
            (spectralDyadicBlock j1 k : ℂ)*weightOneBesselTransform
                (shiftedSourceTest g m1) ((k : ℝ)/q^2) =
              ∫ t : ℝ, shiftedABLMellinDualPhase j1 k t * shiftedABLMellinCirclePhase Q t q * b1 t) ∧
          (∀ (k : ℕ), 0 < k → ∀ (q : ℝ), Q ≤ q → q ≤ 2*Q →
            (spectralDyadicBlock j2 k : ℂ)*weightOneBesselTransform
                (shiftedSourceMajorant m2 T) ((k : ℝ)/q^2) =
              ∫ t : ℝ, shiftedABLMellinDualPhase j2 k t * shiftedABLMellinCirclePhase Q t q * b2 t) ∧
          (1+(m1*T)*((2 : ℝ)^j1/Q^2))^A *
            (∫ t : ℝ, (1+‖t‖)^J*‖b1 t‖) ≤ C*(m1*T) ∧
          (1+(m2*T)*((2 : ℝ)^j2/Q^2))^A *
            (∫ t : ℝ, (1+‖t‖)^J*‖b2 t‖) ≤ C*(m2*T) := by
  have hM (i : Fin 2) : 0 ≤ (fun _ : Fin 2 => Real.log 3) i := Real.log_nonneg (by norm_num)
  obtain ⟨C₁,hC₁,hfirst⟩ := shiftedABLSourceTest_bounds shiftedABLMellinWindow
    shiftedABLMellinExponent _ hM shiftedABLMellinWindow_support A J Cg hCg
  obtain ⟨C₂,hC₂,hsecond⟩ := shiftedABLSourceMajorant_bounds shiftedABLMellinWindow
    shiftedABLMellinExponent _ hM shiftedABLMellinWindow_support A J
  refine ⟨C₁+C₂,by positivity, ?_⟩
  intro g hg T m1 m2 hT hm1 hm2 hgs hscale1 hscale2 hderiv Q hQ j1 j2
  obtain ⟨b1,hb1,hb1mom⟩ := (hfirst g hg T m1 hT hm1 hgs hscale1 hderiv).2.2
    ((2 : ℝ)^j1/Q^2) (by positivity)
  obtain ⟨b2,hb2,hb2mom⟩ := (hsecond T m2 hT hm2 hscale2).2.2
    ((2 : ℝ)^j2/Q^2) (by positivity)
  refine ⟨b1,b2,shiftedABLMellinKernel_identity _ b1 j1 hQ hb1,
    shiftedABLMellinKernel_identity _ b2 j2 hQ hb2, ?_, ?_⟩
  · exact hb1mom.trans (mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hm1.le hT.le))
  · exact hb2mom.trans (mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hm2.le hT.le))

end ArtinMatthews
