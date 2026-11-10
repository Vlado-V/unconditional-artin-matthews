module

public import ArtinMatthews.ShiftedABLRhoCommonTest
public import ArtinMatthews.MarkedMajorOscillatoryDerivatives
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set Filter OAI
open scoped ContDiff Topology
noncomputable section

/-- A fixed smooth extension of the logarithmic phase is sufficient on
the actual support of the unit-scale common test. -/
theorem shiftedABLRhoCommonTest_unit_oscillatory :
    ∃ B : ℝ → ℝ, ContDiff ℝ ∞ B ∧ ∀ u : ℝ,
      shiftedABLRhoCommonTest 1 u = markedOscillatoryFamily (shiftedABLRhoCommonTest 1 0) B u := by
  let K := Icc (1/3 : ℝ) 2
  have hK : K ⊆ Ioo (1/4 : ℝ) 3 := fun _ hx =>
    ⟨by linarith [hx.1],by linarith [hx.2]⟩
  obtain ⟨η,hη,_,hs,hηone⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    isOpen_Ioo isClosed_Icc hK
  let B : ℝ → ℝ := fun x => (2*Real.pi)*η x*Real.log x
  have hB : ContDiff ℝ ∞ B := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : 0 < x
    · exact (contDiffAt_const.mul hη.contDiffAt).mul (Real.contDiffAt_log.mpr hx.ne')
    · have hzero : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℝ)) x := contDiffAt_const
      apply hzero.congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds (by linarith : x < (1/4 : ℝ))] with y hy
      have hη0 : η y = 0 := by
        by_contra hn
        have hm : y ∈ Function.support η := hn
        rw [hs] at hm
        exact (not_lt_of_ge (le_of_lt hm.1)) (show y < (1/4 : ℝ) from hy)
      simp [B,hη0]
  refine ⟨B,hB,fun u => ?_⟩
  have hSupp (v : ℝ) : tsupport (shiftedABLRhoCommonTest 1 v) ⊆ K := by
    simpa only [K,mul_one] using shiftedABLRhoCommonTest_tsupport 1 v zero_lt_one
  funext x
  by_cases hx : x ∈ K
  · have hx0 : 0 < x := (by norm_num : (0 : ℝ) < 1/3).trans_le hx.1
    have hη1 : η x = 1 := (hηone x).mp hx
    simp only [shiftedABLRhoCommonTest,if_pos hx0,div_one,markedOscillatoryFamily,
      markedOscillatoryPhase,markedRealOscillator,FourierBridge.logPhase,zero_mul,mul_zero,
      Complex.ofReal_zero,Complex.exp_zero,mul_one,B,hη1]
    push_cast
    congr 2
    ring
  · have hz (v : ℝ) : shiftedABLRhoCommonTest 1 v x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hm => hx (hSupp v hm))
    simp only [markedOscillatoryFamily,hz,zero_mul]

theorem shiftedABLRhoCommonTest_rescale (a u : ℝ) (ha : 0 < a) :
    shiftedABLRhoCommonTest a u = fun x => shiftedABLRhoCommonTest 1 u (a⁻¹*x) := by
  funext x
  rw [show a⁻¹*x = x/a by rw [div_eq_mul_inv,mul_comm]]
  simp only [shiftedABLRhoCommonTest,div_one,div_pos_iff_of_pos_right ha]

/-- The source modulation has the sharp degree `j` at derivative order
`j`, with the physical dilation kept explicit. -/
theorem shiftedABLRhoCommonTest_scaled_derivative_bound (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a u Z : ℝ, 0 < a → 1+|u| ≤ Z → ∀ j ≤ J, ∀ x : ℝ,
      (a/Z)^j*‖iteratedDeriv j (shiftedABLRhoCommonTest a u) x‖ ≤ C := by
  obtain ⟨B,hB,he⟩ := shiftedABLRhoCommonTest_unit_oscillatory
  let A := shiftedABLRhoCommonTest 1 0
  let K := Icc (1/3 : ℝ) 2
  have hA := shiftedABLRhoCommonTest_contDiff 1 0 zero_lt_one
  choose C hC hbound using fun j => markedOscillatoryFamily_compact_derivative_bound A B
    hA hB K isCompact_Icc j
  let D : ℝ := 1+∑ j ∈ Finset.range (J+1), C j
  have hD : 0 < D := by
    dsimp [D]
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun j _ => (hC j).le))
  refine ⟨D,hD,?_⟩
  intro a u Z ha hZ j hj x
  have hZ₀ : 0 < Z := by linarith [abs_nonneg u]
  by_cases hx : x ∈ Icc (a/3) (2*a)
  · have hxa : a⁻¹*x ∈ K := by
      rw [show a⁻¹*x = x/a by rw [div_eq_mul_inv,mul_comm]]
      exact ⟨(le_div_iff₀ ha).mpr (by rw [show (1/3 : ℝ)*a = a/3 by ring]; exact hx.1),
        (div_le_iff₀ ha).mpr hx.2⟩
    have hunit : ‖iteratedDeriv j (shiftedABLRhoCommonTest 1 u) (a⁻¹*x)‖ ≤ C j*(1+|u|)^j := by
      rw [he u]
      simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hbound j u _ hxa
    have hf := (shiftedABLRhoCommonTest_contDiff 1 u zero_lt_one).of_le
      (show (j : ℕ∞ω) ≤ ∞ by simp)
    have hCj : C j ≤ D := by
      have h := Finset.single_le_sum (fun k _ => (hC k).le)
        (Finset.mem_range.mpr (show j < J+1 by omega))
      dsimp [D]
      linarith
    rw [shiftedABLRhoCommonTest_rescale a u ha,iteratedDeriv_comp_const_smul hf,
      norm_smul,Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr ha.le) _),← mul_assoc,← mul_pow]
    have hscale : a/Z*a⁻¹ = 1/Z := by field_simp [ha.ne',hZ₀.ne']
    rw [hscale]
    have hq : (1+|u|)/Z ≤ 1 := (div_le_one hZ₀).mpr hZ
    calc
      _ ≤ (1/Z)^j*(C j*(1+|u|)^j) := mul_le_mul_of_nonneg_left hunit (by positivity)
      _ = C j*((1+|u|)/Z)^j := by rw [div_pow,div_pow,one_pow]; ring
      _ ≤ C j := mul_le_of_le_one_right (hC j).le (pow_le_one₀ (by positivity) hq)
      _ ≤ _ := hCj
  · have hz : shiftedABLRhoCommonTest a u =ᶠ[𝓝 x] (0 : ℝ → ℂ) :=
      notMem_tsupport_iff_eventuallyEq.mp (fun hm => hx (shiftedABLRhoCommonTest_tsupport a u ha hm))
    rw [hz.iteratedDeriv_eq j]
    change (a/Z)^j*‖iteratedDeriv j (fun _ : ℝ => (0 : ℂ)) x‖ ≤ D
    simpa only [iteratedDeriv_const,ite_self,norm_zero,mul_zero] using hD.le

end
end ArtinMatthews
