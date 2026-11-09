module

public import ArtinMatthews.ShiftedABLRhoCommonDerivative
public import ArtinMatthews.SpectralABLDyadicDerivative
public import ArtinMatthews.SpectralDyadicPartition


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set Finset
open scoped ContDiff BigOperators
noncomputable section

def shiftedABLRhoCommonDyadicScale (a : ℝ) (k : ℕ) (right : Bool) : ℝ :=
  (a/4)*(2 : ℝ)^k/(if right then spectralDyadicRatio else 1)

def shiftedABLRhoCommonDyadicTest (a u : ℝ) (k : ℕ) (right : Bool) (x : ℝ) : ℂ :=
  (spectralDyadicWeight (x/shiftedABLRhoCommonDyadicScale a k right) : ℂ)*
    shiftedABLRhoCommonTest a u x

theorem shiftedABLRhoCommonDyadicScale_pos {a : ℝ} (ha : 0 < a) (k : ℕ) (right : Bool) :
    0 < shiftedABLRhoCommonDyadicScale a k right := by
  have hρ := spectralDyadicRatio_pos
  cases right <;> simp only [shiftedABLRhoCommonDyadicScale,Bool.false_eq_true,Bool.true_eq,ite_false,ite_true]
  all_goals positivity

theorem shiftedABLRhoCommonDyadicScale_bounds {a : ℝ} (ha : 0 < a) {k : ℕ} (hk : k < 4)
    (right : Bool) : a/(4*spectralDyadicRatio) ≤ shiftedABLRhoCommonDyadicScale a k right ∧
      shiftedABLRhoCommonDyadicScale a k right ≤ 2*a := by
  let h : ℝ := if right then spectralDyadicRatio else 1
  have hh : 1 ≤ h := by cases right <;> simp [h,spectralDyadicRatio_one_lt.le]
  have hhρ : h ≤ spectralDyadicRatio := by cases right <;> simp [h,spectralDyadicRatio_one_lt.le]
  have hh0 : 0 < h := zero_lt_one.trans_le hh
  have hpow₁ : (1 : ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
  have hpow₈ : (2 : ℝ)^k ≤ 8 :=
    (pow_le_pow_right₀ (by norm_num) (show k ≤ 3 by omega)).trans_eq (by norm_num)
  change a/(4*spectralDyadicRatio) ≤ (a/4)*2^k/h ∧ (a/4)*2^k/h ≤ 2*a
  constructor
  · calc
      _ = (a/4)/spectralDyadicRatio := by ring
      _ ≤ (a/4)/h := div_le_div_of_nonneg_left (by positivity) hh0 hhρ
      _ ≤ _ := div_le_div_of_nonneg_right (le_mul_of_one_le_right (by positivity) hpow₁) hh0.le
  · calc
      _ ≤ (a/4)*2^k := div_le_self (by positivity) hh
      _ ≤ (a/4)*8 := mul_le_mul_of_nonneg_left hpow₈ (by positivity)
      _ = _ := by ring

theorem shiftedABLRhoCommonDyadicTest_contDiff {a : ℝ} (ha : 0 < a) (u : ℝ) (k : ℕ)
    (right : Bool) : ContDiff ℝ ∞ (shiftedABLRhoCommonDyadicTest a u k right) := by
  have h := spectralDyadicWeight_contDiff.comp (contDiff_id.div_const (shiftedABLRhoCommonDyadicScale a k right))
  exact (Complex.ofRealCLM.contDiff.comp h).mul (shiftedABLRhoCommonTest_contDiff a u ha)

theorem shiftedABLRhoCommonDyadicTest_tsupport {a : ℝ} (ha : 0 < a) (u : ℝ) (k : ℕ)
    (right : Bool) : let d := shiftedABLRhoCommonDyadicScale a k right
    tsupport (shiftedABLRhoCommonDyadicTest a u k right) ⊆ Icc d (2*d) := by
  intro d
  have hd : 0 < d := shiftedABLRhoCommonDyadicScale_pos ha k right
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hw : x/d ∈ Function.support spectralDyadicWeight := by
    intro he
    exact hx (by simp [shiftedABLRhoCommonDyadicTest,show shiftedABLRhoCommonDyadicScale a k right = d from rfl,he])
  have h := spectralDyadicWeight_support hw
  exact ⟨(one_le_div hd).mp h.1,(div_le_iff₀ hd).mp h.2⟩

theorem shiftedABLRhoCommonDyadicTest_derivative_bound (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a u Z : ℝ, 0 < a → 1+|u| ≤ Z → ∀ (k : ℕ), k < 4 →
      ∀ (right : Bool), let d := shiftedABLRhoCommonDyadicScale a k right
      ∀ j ≤ J, ∀ x ∈ Icc d (2*d),
        (d/Z)^j*‖iteratedDeriv j (shiftedABLRhoCommonDyadicTest a u k right) x‖ ≤ C := by
  obtain ⟨D,hD,hf⟩ := shiftedABLRhoCommonTest_scaled_derivative_bound J
  let φ : ℝ → ℂ := fun v => (spectralDyadicWeight v : ℂ)
  have hφ : ContDiff ℝ ∞ φ := Complex.ofRealCLM.contDiff.comp spectralDyadicWeight_contDiff
  obtain ⟨E,hE,hprod⟩ := spectralDyadic_scaled_mul_deriv_bound φ hφ.contDiffOn J
  refine ⟨E*(2^J*D),by positivity,?_⟩
  intro a u Z ha hZ k hk right d j hj x hx
  have hZ₁ : 1 ≤ Z := (by linarith [abs_nonneg u] : 1 ≤ 1+|u|).trans hZ
  have hZ₀ : 0 < Z := zero_lt_one.trans_le hZ₁
  have hd : 0 < d := shiftedABLRhoCommonDyadicScale_pos ha k right
  have hda : d ≤ 2*a := (shiftedABLRhoCommonDyadicScale_bounds ha hk right).2
  have hratio : d/a ≤ 2 := (div_le_iff₀ ha).mpr hda
  have hcoeff : ∀ i ≤ J, ∀ y ∈ Icc d (2*d),
      (d/Z)^i*‖iteratedDeriv i (shiftedABLRhoCommonTest a u) y‖ ≤ 2^J*D := by
    intro i hi y _
    have hp : (d/a)^i ≤ (2 : ℝ)^J :=
      (pow_le_pow_left₀ (by positivity) hratio i).trans (pow_le_pow_right₀ (by norm_num) hi)
    calc
      _ = (d/a)^i*((a/Z)^i*‖iteratedDeriv i (shiftedABLRhoCommonTest a u) y‖) := by
        rw [show d/Z = (d/a)*(a/Z) by field_simp [ha.ne',hZ₀.ne'],mul_pow]
        ring
      _ ≤ _ := mul_le_mul hp (hf a u Z ha hZ i hi y) (by positivity) (by positivity)
  have hb : d/Z ≤ d := div_le_self hd.le hZ₁
  exact hprod d (d/Z) (2^J*D) (shiftedABLRhoCommonTest a u) hd (by positivity) hb (by positivity)
    (shiftedABLRhoCommonTest_contDiff a u ha) hcoeff j hj x hx

theorem shiftedABLRhoCommonTest_dyadic_partition {a : ℝ} (ha : 0 < a) (u : ℝ) :
    shiftedABLRhoCommonTest a u = fun x =>
      ∑ i ∈ (range 4 ×ˢ (univ : Finset Bool)), shiftedABLRhoCommonDyadicTest a u i.1 i.2 x := by
  funext x
  let f := shiftedABLRhoCommonTest a u
  let y := x/(a/4)
  by_cases hx : x ∈ Icc (a/3) (2*a)
  · have hy₁ : 1 ≤ y := (one_le_div (by positivity : 0 < a/4)).mpr (by linarith [hx.1])
    have hy₈ : y ≤ 8 := (div_le_iff₀ (by positivity : 0 < a/4)).mpr (by linarith [hx.2])
    have h₁ : spectralDyadicRatio ≤ spectralDyadicRatio*y := by
      exact le_mul_of_one_le_right spectralDyadicRatio_pos.le hy₁
    have h₂ : y/(spectralDyadicRatio*(2 : ℝ)^3) ≤ 1 := by
      apply (div_le_one (mul_pos spectralDyadicRatio_pos (by positivity))).mpr
      rw [show (2 : ℝ)^3 = 8 by norm_num]
      linarith [spectralDyadicRatio_one_lt]
    have hsum : (∑ k ∈ range 4, spectralDyadicBlock k y) = 1 := by
      rw [show (4 : ℕ) = 3+1 by decide,spectralDyadicBlock_partial_sum,
        spectralDyadicStep_one h₁,spectralDyadicStep_zero h₂,sub_zero]
    have harg₀ (k : ℕ) : x/shiftedABLRhoCommonDyadicScale a k false = y/(2 : ℝ)^k := by
      simp only [shiftedABLRhoCommonDyadicScale,Bool.false_eq_true,ite_false,div_one,y]
      field_simp [ha.ne',show (2 : ℝ)^k ≠ 0 by positivity] <;> ring
    have harg₁ (k : ℕ) : x/shiftedABLRhoCommonDyadicScale a k true = spectralDyadicRatio*y/(2 : ℝ)^k := by
      simp only [shiftedABLRhoCommonDyadicScale,Bool.true_eq,ite_true,y]
      field_simp [ha.ne',spectralDyadicRatio_pos.ne',show (2 : ℝ)^k ≠ 0 by positivity] <;> ring
    rw [sum_product]
    calc
      f x = ((∑ k ∈ range 4, spectralDyadicBlock k y : ℝ) : ℂ)*f x := by rw [hsum,Complex.ofReal_one,one_mul]
      _ = ∑ k ∈ range 4, ((spectralDyadicBlock k y : ℝ) : ℂ)*f x := by
        push_cast
        rw [sum_mul]
      _ = _ := by
        apply sum_congr rfl
        intro k _
        rw [Fintype.sum_bool]
        simp only [shiftedABLRhoCommonDyadicTest,harg₀,harg₁,spectralDyadicBlock,Complex.ofReal_add,f]
        ring
  · have hz : f x = 0 := image_eq_zero_of_notMem_tsupport
      (fun hm => hx (shiftedABLRhoCommonTest_tsupport a u ha hm))
    change f x = ∑ i ∈ (range 4 ×ˢ (univ : Finset Bool)),
      ((spectralDyadicWeight (x/shiftedABLRhoCommonDyadicScale a i.1 i.2) : ℝ) : ℂ)*f x
    simp only [hz,mul_zero,sum_const_zero]

end
end ArtinMatthews
