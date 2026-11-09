module

public import ArtinMatthews.ShiftedABLMellinCoefficient
public import ArtinMatthews.ShiftedConvolutionWeights
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics


set_option backward.privateInPublic true
@[expose] public section

/-! The checked Wilton and Parseval estimate for the actual interlaced
Mellin coefficient, including the lowest three-sample window. -/

noncomputable section
open Set OAI UpperHalfPlane
open scoped ContDiff BigOperators MatrixGroups

namespace ArtinMatthews

private def shiftedABLWindowSchwartz : SchwartzMap ℝ ℂ :=
  (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (show Function.support (fun x => (spectralDyadicWeight x : ℂ)) ⊆ Icc (1 : ℝ) 2 from by
      intro x hx
      exact spectralDyadicWeight_support (fun h => hx (by simp [h])))).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp spectralDyadicWeight_contDiff)

private theorem shiftedABLWindowSchwartz_apply (x : ℝ) :
    shiftedABLWindowSchwartz x = (spectralDyadicWeight x : ℂ) := rfl

theorem shiftedABLMellinDualPhase_norm_le (j k : ℕ) (t : ℝ) :
    ‖shiftedABLMellinDualPhase j k t‖ ≤ 2 := by
  rw [shiftedABLMellinDualPhase,norm_mul,norm_shifted_logPhase,mul_one,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (spectralDyadicBlock_nonneg _ _)]
  unfold spectralDyadicBlock
  linarith [spectralDyadicWeight_le_one ((k : ℝ)/(2 : ℝ)^j),
    spectralDyadicWeight_le_one (spectralDyadicRatio*(k : ℝ)/(2 : ℝ)^j)]

theorem shiftedABLMellinDualPhase_variation :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℕ) (t : ℝ),
      sampledVariation (2*2^j+1) (fun k => shiftedABLMellinDualPhase j k t) ≤ C*(1+|t|) := by
  let w := shiftedABLWindowSchwartz
  let B := SchwartzMap.seminorm ℝ 0 0 w
  let L := SchwartzMap.seminorm ℝ 0 1 w
  let D := 3*(L+4*Real.pi*B)
  have hB : 0 ≤ B := apply_nonneg _ _
  have hL : 0 ≤ L := apply_nonneg _ _
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨14+3*D, by linarith, ?_⟩
  intro j t
  let v (k : ℕ) := shiftedABLMellinDualPhase j k t
  have hv (k : ℕ) : ‖v k‖ ≤ 2 := shiftedABLMellinDualPhase_norm_le j k t
  have ht : 1 ≤ 1+|t| := le_add_of_nonneg_right (abs_nonneg t)
  by_cases hj : j = 0
  · have hN : 2*2^j+1 = (3 : ℕ) := by simp [hj]
    change sampledVariation (2*2^j+1) v ≤ _
    rw [hN, sampledVariation]
    have hdiff (k : ℕ) : ‖v k-v (k+1)‖ ≤ 4 := by
      linarith [norm_sub_le (v k) (v (k+1)),hv k,hv (k+1)]
    calc
      _ ≤ 2+∑ _k ∈ Finset.range 3, (4 : ℝ) :=
        add_le_add (hv 3) (Finset.sum_le_sum (fun k _ => hdiff k))
      _ ≤ _ := by simp; nlinarith [mul_nonneg hD (abs_nonneg t)]
  let K : ℝ := 2^j
  let K' := K/spectralDyadicRatio
  let τ := -(2*Real.pi*t)
  have hK0 : 0 < K := by dsimp [K]; positivity
  have hK2 : 2 ≤ K := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (Nat.one_le_iff_ne_zero.mpr hj)
  have hK : 1 ≤ K := by linarith
  have hratio := spectralDyadicRatio_pos
  have hratio2 : spectralDyadicRatio ≤ 2 := by
    nlinarith [spectralDyadicRatio_sq, sq_nonneg (spectralDyadicRatio-1)]
  have hK' : 1 ≤ K' := (one_le_div hratio).2 (hratio2.trans hK2)
  have hK'0 : 0 < K' := zero_lt_one.trans_le hK'
  have hw : Function.support w ⊆ Icc (1 : ℝ) 2 := by
    intro x hx
    apply spectralDyadicWeight_support
    intro h
    apply hx
    change shiftedABLWindowSchwartz x = 0
    simp [shiftedABLWindowSchwartz_apply,h]
  have hsplit (k : ℕ) : v k = FourierBridge.logPhase t (-Real.log K) *
      (shiftedDyadicWeight w K τ k + shiftedDyadicWeight w K' τ k) := by
    have harg : (k : ℝ)/K' = spectralDyadicRatio*(k : ℝ)/K := by
      dsimp [K']
      field_simp [hK0.ne',hratio.ne'] <;> ring
    by_cases hk : k = 0
    · subst k
      simp [v,shiftedABLMellinDualPhase,spectralDyadicBlock,shiftedDyadicWeight,w,
        shiftedABLWindowSchwartz_apply,spectralDyadicWeight_zero_of_le_one (by norm_num : (0 : ℝ) ≤ 1)]
    have hk0 : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    change (spectralDyadicBlock j k : ℂ)*FourierBridge.logPhase t (Real.log ((k : ℝ)/K)) = _
    rw [logPhase_log_div_eq t k K hk0 hK0]
    simp only [spectralDyadicBlock,shiftedDyadicWeight,w,shiftedABLWindowSchwartz_apply,
      harg,Complex.ofReal_add]
    change _ = _ * (shiftedMellinPhase τ k * _ + shiftedMellinPhase τ k * _)
    ring
  have hτ : |τ| = 2*Real.pi*|t| := by
    dsimp [τ]
    rw [abs_neg,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2*Real.pi)]
  have hdiff (k : ℕ) : ‖v k-v (k+1)‖ ≤ D*(1+|t|)/K := by
    rw [hsplit k,hsplit (k+1),←mul_sub,norm_mul,norm_shifted_logPhase,one_mul]
    have he : (shiftedDyadicWeight w K τ k+shiftedDyadicWeight w K' τ k) -
        (shiftedDyadicWeight w K τ (k+1)+shiftedDyadicWeight w K' τ (k+1)) =
        (shiftedDyadicWeight w K τ k-shiftedDyadicWeight w K τ (k+1)) +
        (shiftedDyadicWeight w K' τ k-shiftedDyadicWeight w K' τ (k+1)) := by ring
    rw [he]
    let A := L + 2 * |τ| * B
    have hA : 0 ≤ A := by dsimp [A]; positivity
    calc
      _ ≤ _ := norm_add_le _ _
      _ ≤ A/K+A/K' := add_le_add (shiftedDyadicWeight_difference w hw K τ hK k)
        (shiftedDyadicWeight_difference w hw K' τ hK' k)
      _ = (1+spectralDyadicRatio)*A/K := by
        dsimp [K']
        field_simp [hK0.ne',hratio.ne'] <;> ring
      _ ≤ 3*A/K := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) hA) hK0.le
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ hK0.le
        dsimp [A,D]
        rw [hτ]
        nlinarith [mul_nonneg hL (abs_nonneg t),
          mul_nonneg (by positivity : 0 ≤ 4*Real.pi) hB]
  let N : ℕ := 2*2^j+1
  have hN : (N : ℝ) ≤ 3*K := by
    change ((2*2^j+1 : ℕ) : ℝ) ≤ _
    push_cast
    change 2*K+1 ≤ _
    linarith
  change sampledVariation N v ≤ _
  unfold sampledVariation
  calc
    _ ≤ 2+∑ _k ∈ Finset.range N, D*(1+|t|)/K :=
      add_le_add (hv N) (Finset.sum_le_sum (fun k _ => hdiff k))
    _ = 2+(N : ℝ)*(D*(1+|t|)/K) := by simp
    _ ≤ 2+(3*K)*(D*(1+|t|)/K) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hN (by positivity))
    _ = 2+3*D*(1+|t|) := by field_simp [hK0.ne'] <;> ring
    _ ≤ _ := by nlinarith [mul_nonneg hD (abs_nonneg t)]

private theorem shiftedABLDualWindow_range (j : ℕ) :
    insert 0 (shiftedABLDualWindow j) = Finset.range (2*2^j+1) := by
  ext k
  simp only [shiftedABLDualWindow,Finset.mem_insert,Finset.mem_Icc,Finset.mem_range]
  omega

/-- The genuine q-independent coefficient satisfies the original
congruence-uniform Wilton–Parseval estimate for every signed subset. -/
theorem shiftedABLMellinRhoCoefficient_energy
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 1) (hperiod : (1 : ℝ) ∈ Γ.strictPeriods)
    (χ : SevenEighths.HeckeFamily.Character)
    (hcoeff : ∀ k, (qExpansion 1 f).coeff k = idealThetaCoeff χ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D m3 m4 : ℕ) [NeZero D], 0 < m4 →
      ∀ (d : ℕ × ℕ) (z : ℝ × ℝ) (R : Finset ℤ),
        let K1 : ℝ := 2^d.1
        let K2 : ℝ := 2^d.2
        (∑ ρ ∈ R, ‖shiftedABLMellinRhoCoefficient χ D m3 m4 d ρ z‖^2) ≤
          C*K1*K2*(Real.log (6*K1))^2*(1+|z.1|)^2 := by
  obtain ⟨C₀,hC₀,hbase⟩ := weightOne_shiftedConvolution_energy f hperiod
  obtain ⟨C₁,hC₁,hvar⟩ := shiftedABLMellinDualPhase_variation
  refine ⟨36*C₀*C₁^2+1,by positivity,?_⟩
  intro D m3 m4 inst hm4 d z R K1 K2
  let N1 : ℕ := 2*2^d.1+1
  let N2 : ℕ := 2*2^d.2+1
  let v1 (k : ℕ) := shiftedABLMellinDualPhase d.1 k z.1
  let v2 (k : ℕ) := shiftedABLMellinDualPhase d.2 k z.2
  have hN1 : 2 ≤ N1 := by
    have hpow : 0 < (2 : ℕ)^d.1 := by positivity
    dsimp [N1]
    omega
  have hK1 : 1 ≤ K1 := one_le_pow₀ (by norm_num)
  have hK2 : 1 ≤ K2 := one_le_pow₀ (by norm_num)
  have hn1 : (N1 : ℝ) ≤ 3*K1 := by dsimp [N1]; push_cast; change 2*K1+1 ≤ _; linarith
  have hn2 : (N2 : ℝ) ≤ 3*K2 := by dsimp [N2]; push_cast; change 2*K2+1 ≤ _; linarith
  have hlog0 : 0 ≤ Real.log (2*(N1 : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2*N1))
  have hlog : Real.log (2*(N1 : ℝ)) ≤ Real.log (6*K1) :=
    Real.log_le_log (by positivity) (by linarith)
  have hvar0 : 0 ≤ sampledVariation N1 v1 := by unfold sampledVariation; positivity
  have heq (ρ : ℤ) : shiftedConvolutionCoeff (Finset.range N1) (Finset.range N2) m3 m4 D
      (fun k => (qExpansion 1 f).coeff k*v1 k)
      (fun k => (qExpansion 1 f).coeff k*v2 k) ρ =
      shiftedABLMellinRhoCoefficient χ D m3 m4 d ρ z := by
    change shiftedConvolutionCoeff (Finset.range (2*2^d.1+1)) (Finset.range (2*2^d.2+1))
      m3 m4 D _ _ ρ = _
    rw [←shiftedABLDualWindow_range d.1,←shiftedABLDualWindow_range d.2]
    simp [shiftedConvolutionCoeff,shiftedABLMellinRhoCoefficient,shiftedABLDualWindow,
      hcoeff,idealThetaCoeff_zero,v1,v2]
  have h := hbase N1 N2 m3 m4 D hN1 hm4 v1 v2 2 (by norm_num)
    (fun k _ => shiftedABLMellinDualPhase_norm_le d.2 k z.2) R
  simp_rw [heq] at h
  have hv := hvar d.1 z.1
  calc
    _ ≤ C₀*N1*N2*(Real.log (2*N1))^2*(sampledVariation N1 v1)^2*2^2 := h
    _ ≤ C₀*(3*K1)*(3*K2)*(Real.log (6*K1))^2*(C₁*(1+|z.1|))^2*2^2 := by
      gcongr
    _ = (36*C₀*C₁^2)*K1*K2*(Real.log (6*K1))^2*(1+|z.1|)^2 := by ring
    _ ≤ _ := by gcongr; linarith


/-- Equation (5.6) for the exact Mellin coefficient, with the
logarithm absorbed at any prescribed positive exponent. -/
theorem shiftedABLMellinRhoCoefficient_norm_le
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 1) (hperiod : (1 : ℝ) ∈ Γ.strictPeriods)
    (χ : SevenEighths.HeckeFamily.Character)
    (hcoeff : ∀ k, (qExpansion 1 f).coeff k = idealThetaCoeff χ k)
    (ν : ℝ) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D m3 m4 : ℕ) [NeZero D], 0 < m4 →
      ∀ (d : ℕ × ℕ) (z : ℝ × ℝ) (R : Finset ℤ),
        let K1 : ℝ := 2^d.1
        let K2 : ℝ := 2^d.2
        Real.sqrt (∑ ρ ∈ R, ‖shiftedABLMellinRhoCoefficient χ D m3 m4 d ρ z‖^2) ≤
          C*(K1*K2)^((1+ν)/2)*(1+|z.1|) := by
  obtain ⟨C₀,hC₀,henergy⟩ := shiftedABLMellinRhoCoefficient_energy f hperiod χ hcoeff
  let e := ν/2
  have he : 0 < e := by dsimp [e]; positivity
  have hlog6 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  let B := Real.log 6+1/e
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨Real.sqrt C₀*B, by positivity,?_⟩
  intro D m3 m4 inst hm4 d z R K1 K2
  have hK1 : 1 ≤ K1 := one_le_pow₀ (by norm_num)
  have hK2 : 1 ≤ K2 := one_le_pow₀ (by norm_num)
  have hK10 : 0 < K1 := zero_lt_one.trans_le hK1
  have hK20 : 0 < K2 := zero_lt_one.trans_le hK2
  have hKprod : K1 ≤ K1*K2 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hK2 hK10.le
  have hp := Real.one_le_rpow hK1 he.le
  have hlog0 : 0 ≤ Real.log (6*K1) := Real.log_nonneg (by linarith)
  have hlog : Real.log (6*K1) ≤ B*(K1*K2)^e := by
    calc
      _ = Real.log 6+Real.log K1 := Real.log_mul (by norm_num) hK10.ne'
      _ ≤ Real.log 6+K1^e/e := add_le_add le_rfl (Real.log_le_rpow_div hK10.le he)
      _ ≤ Real.log 6*K1^e+K1^e/e := add_le_add
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hlog6) le_rfl
      _ = B*K1^e := by dsimp [B]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hK10.le hKprod he.le) hB.le
  have htime : 0 ≤ 1+|z.1| := by positivity
  calc
    _ ≤ Real.sqrt (C₀*K1*K2*(Real.log (6*K1))^2*(1+|z.1|)^2) :=
      Real.sqrt_le_sqrt (henergy D m3 m4 hm4 d z R)
    _ = Real.sqrt C₀*(K1*K2)^(1/2 : ℝ)*Real.log (6*K1)*(1+|z.1|) := by
      rw [show C₀*K1*K2*(Real.log (6*K1))^2*(1+|z.1|)^2 =
        C₀*((K1*K2)*((Real.log (6*K1))^2*(1+|z.1|)^2)) by ring]
      rw [Real.sqrt_mul hC₀.le,Real.sqrt_mul (mul_nonneg hK10.le hK20.le),
        Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hlog0,Real.sqrt_sq htime,
        Real.sqrt_eq_rpow (K1*K2)]
      ring
    _ ≤ Real.sqrt C₀*(K1*K2)^(1/2 : ℝ)*(B*(K1*K2)^e)*(1+|z.1|) := by
      gcongr
    _ = _ := by
      rw [show (1+ν)/2 = (1/2 : ℝ)+e by dsimp [e]; ring,Real.rpow_add (mul_pos hK10 hK20)]
      ring

end ArtinMatthews
