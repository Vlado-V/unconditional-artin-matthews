module

public import ArtinMatthews.ShiftedABLRhoLogDensity


set_option backward.privateInPublic true
@[expose] public section

/-! One fixed compact log plateau gives a common spatial test for every
frequency in a signed dyadic rho block. -/

noncomputable section
open Set MeasureTheory Filter OAI
open scoped ContDiff
namespace ArtinMatthews

theorem shiftedABLRhoPlateau_exists :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ Icc (-Real.log 3) (Real.log 2) ∧
      (∀ v, 0 ≤ χ v ∧ χ v ≤ 1) ∧
      ∀ v ∈ Icc (-Real.log 2) (Real.log 2/2), χ v = 1 := by
  have h₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h₃ : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have hS : Icc (-Real.log 2) (Real.log 2/2) ⊆ Ioo (-Real.log 3) (Real.log 2) := by
    intro v hv
    exact ⟨by linarith [hv.1],by linarith [hv.2]⟩
  obtain ⟨χ,hχ,h01,hSupp,hOne⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    isOpen_Ioo isClosed_Icc hS
  have hT : tsupport χ ⊆ Icc (-Real.log 3) (Real.log 2) := by
    rw [tsupport,hSupp]
    exact closure_minimal Ioo_subset_Icc_self isClosed_Icc
  exact ⟨χ,hχ,isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hT,hT,
    fun v => h01 ⟨v,rfl⟩,fun v hv => (hOne v).mp hv⟩

def shiftedABLRhoPlateau : ℝ → ℝ := shiftedABLRhoPlateau_exists.choose

theorem shiftedABLRhoPlateau_properties :
    ContDiff ℝ ∞ shiftedABLRhoPlateau ∧ HasCompactSupport shiftedABLRhoPlateau ∧
      tsupport shiftedABLRhoPlateau ⊆ Icc (-Real.log 3) (Real.log 2) ∧
      (∀ v, 0 ≤ shiftedABLRhoPlateau v ∧ shiftedABLRhoPlateau v ≤ 1) ∧
      ∀ v ∈ Icc (-Real.log 2) (Real.log 2/2), shiftedABLRhoPlateau v = 1 :=
  shiftedABLRhoPlateau_exists.choose_spec

def shiftedABLRhoCommonTest (a t x : ℝ) : ℂ :=
  if 0 < x then
    (shiftedABLRhoPlateau (Real.log (x/a)) : ℂ)*FourierBridge.logPhase t (Real.log (x/a))
  else 0

theorem shiftedABLRhoCommonTest_norm_le (a t x : ℝ) : ‖shiftedABLRhoCommonTest a t x‖ ≤ 1 := by
  unfold shiftedABLRhoCommonTest
  split_ifs with hx
  · rw [norm_mul,norm_shifted_logPhase,mul_one,Complex.norm_real,Real.norm_of_nonneg
      (shiftedABLRhoPlateau_properties.2.2.2.1 _).1]
    exact (shiftedABLRhoPlateau_properties.2.2.2.1 _).2
  · simp

theorem shiftedABLRhoCommonTest_tsupport (a t : ℝ) (ha : 0 < a) :
    tsupport (shiftedABLRhoCommonTest a t) ⊆ Icc (a/3) (2*a) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hx₀ : 0 < x := by
    by_contra h
    exact hx (if_neg h)
  have hxCut : Real.log (x/a) ∈ tsupport shiftedABLRhoPlateau := by
    apply subset_tsupport
    intro h
    apply hx
    simp [shiftedABLRhoCommonTest,hx₀,h]
  have hV := shiftedABLRhoPlateau_properties.2.2.1 hxCut
  have hExp₁ := Real.exp_le_exp.mpr hV.1
  have hExp₂ := Real.exp_le_exp.mpr hV.2
  rw [Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ) < 3),
    Real.exp_log (div_pos hx₀ ha)] at hExp₁
  rw [Real.exp_log (div_pos hx₀ ha),Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hExp₂
  exact ⟨(show a/3 = (3 : ℝ)⁻¹*a by ring).trans_le ((le_div_iff₀ ha).mp hExp₁),
    (div_le_iff₀ ha).mp hExp₂⟩

theorem shiftedABLRhoCommonTest_contDiff (a t : ℝ) (ha : 0 < a) :
    ContDiff ℝ ∞ (shiftedABLRhoCommonTest a t) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : 0 < x
  · have hχ := Complex.ofRealCLM.contDiff.comp shiftedABLRhoPlateau_properties.1
    have hPhase : ContDiff ℝ ∞ (FourierBridge.logPhase t) := by
      change ContDiff ℝ ∞ (fun y : ℝ =>
        Complex.exp (Complex.ofRealCLM (2*Real.pi*t*y)*Complex.I))
      fun_prop
    have hLinear : ContDiffAt ℝ ∞ (fun y : ℝ => y/a) x := (contDiff_id.div_const a).contDiffAt
    have hOuter : ContDiffAt ℝ ∞ Real.log (x/a) := Real.contDiffAt_log.mpr (div_pos hx ha).ne'
    have hLog : ContDiffAt ℝ ∞ (fun y : ℝ => Real.log (y/a)) x := by
      simpa only [Function.comp_def] using hOuter.comp x hLinear
    apply ((hχ.mul hPhase).contDiffAt.comp x hLog).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hx] with y hy
    exact if_pos hy
  · have hZero : x ∉ tsupport (shiftedABLRhoCommonTest a t) := fun h =>
      hx ((by positivity : 0 < a/3).trans_le ((shiftedABLRhoCommonTest_tsupport a t ha) h).1)
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hZero)

theorem shiftedABLRhoCommonTest_compact (a t : ℝ) (ha : 0 < a) :
    HasCompactSupport (shiftedABLRhoCommonTest a t) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (shiftedABLRhoCommonTest_tsupport a t ha)

theorem shiftedABLRhoLogProfile_split (z : ℝ × ℝ) (v b : ℝ)
    (hb₀ : 0 ≤ b) (hb₁ : b ≤ Real.log 2/2) :
    shiftedABLRhoLogProfile z (v-b) =
      ∫ t : ℝ, shiftedABLRhoFourierDensity t*FourierBridge.logPhase (t+shiftedABLRhoHeight z) (-b)*
        ((shiftedABLRhoPlateau v : ℂ)*FourierBridge.logPhase (t+shiftedABLRhoHeight z) v) := by
  have hCut : (shiftedABLRhoPlateau v : ℂ)*shiftedABLRhoLogProfile z (v-b) =
      shiftedABLRhoLogProfile z (v-b) := by
    by_cases h : shiftedABLRhoLogBase (v-b) = 0
    · simp [shiftedABLRhoLogProfile,h]
    · have hv := shiftedABLRhoLogBase_support h
      rw [shiftedABLRhoPlateau_properties.2.2.2.2 v ⟨by linarith [hv.1],by linarith [hv.2]⟩,
        Complex.ofReal_one,one_mul]
  calc
    _ = (shiftedABLRhoPlateau v : ℂ)*shiftedABLRhoLogProfile z (v-b) := hCut.symm
    _ = ∫ t : ℝ, (shiftedABLRhoPlateau v : ℂ)*
        (shiftedABLRhoFourierDensity t*FourierBridge.logPhase (t+shiftedABLRhoHeight z) (v-b)) := by
      rw [shiftedABLRhoLogProfile_inverse,integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      rw [sub_eq_add_neg,FourierBridge.logPhase_add]
      ring

end ArtinMatthews
