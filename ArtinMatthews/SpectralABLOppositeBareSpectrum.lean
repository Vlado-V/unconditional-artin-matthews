module

public import ArtinMatthews.SpectralABLOppositeKWeight
public import ArtinMatthews.SpectralBareTestDominance


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Filter Complex
open scoped MatrixGroups ContDiff Topology
noncomputable section

/-- The actual positive exceptional window controls normalized compact
test data on the whole principal axis. -/
theorem spectralABLExceptionalCorrected_one_three_lower (t : ℝ) :
    ((36 : ℝ)^6)⁻¹ ≤ (1+t^2)^2*Real.exp (Real.pi*|t|)*
      ‖spectralABLExceptionalCorrected 1 3 (t : ℂ)‖ := by
  let u : ℝ := 1+t^2
  let E := Real.exp (Real.pi*|t|)
  let P := (t^2+1/4)*(t^2+9/4)*(t^2+25/4)*(t^2+49/4)
  have hu : 0 < u := by dsimp [u]; positivity
  have hpoly : spectralABLExceptionalWindowReal 1 3 t = 4/(t^2+36)^6*P := by
    norm_num [spectralABLExceptionalWindowReal,P,Real.log_one,Real.cos_zero,Finset.prod_range_succ] <;> ring
  have hP : u^4/4 ≤ P := by
    have h0 : u/4 ≤ t^2+1/4 := by dsimp [u]; nlinarith [sq_nonneg t]
    have h1 : u ≤ t^2+9/4 := by dsimp [u]; linarith
    have h2 : u ≤ t^2+25/4 := by dsimp [u]; linarith
    have h3 : u ≤ t^2+49/4 := by dsimp [u]; linarith
    calc
      _ = (u/4)*u*u*u := by ring
      _ ≤ P := by dsimp [P]; gcongr
  have hden : (t^2+36)^6 ≤ (36*u)^6 := pow_le_pow_left₀ (by positivity)
    (by dsimp [u]; nlinarith [sq_nonneg t]) 6
  have hW : 1/((36 : ℝ)^6*u^2) ≤ spectralABLExceptionalWindowReal 1 3 t := by
    rw [hpoly]
    calc
      _ = (4/(36*u)^6)*(u^4/4) := by rw [mul_pow]; field_simp [hu.ne'] <;> ring
      _ ≤ _ := mul_le_mul (div_le_div_of_nonneg_left (by norm_num) (by positivity) hden)
        hP (by positivity) (by positivity)
  have hcosh : Real.cosh (Real.pi*t) ≤ E := by
    have hp : Real.pi*t ≤ Real.pi*|t| :=
      mul_le_mul_of_nonneg_left (le_abs_self t) Real.pi_pos.le
    have hm : -(Real.pi*t) ≤ Real.pi*|t| := by
      rw [← mul_neg]
      exact mul_le_mul_of_nonneg_left (neg_le_abs t) Real.pi_pos.le
    rw [Real.cosh_eq]
    dsimp [E]
    linarith [Real.exp_le_exp.mpr hp,Real.exp_le_exp.mpr hm]
  rw [spectralABLExceptionalCorrected_norm_real]
  have hC := Real.cosh_pos (Real.pi*t)
  have hW' : 1/((36 : ℝ)^6*u^2) ≤ E*
      (spectralABLExceptionalWindowReal 1 3 t/Real.cosh (Real.pi*t)) := by
    calc
      _ ≤ spectralABLExceptionalWindowReal 1 3 t := hW
      _ = Real.cosh (Real.pi*t)*
          (spectralABLExceptionalWindowReal 1 3 t/Real.cosh (Real.pi*t)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcosh
        (div_nonneg (spectralABLExceptionalWindowReal_nonneg 1 3 t) hC.le)
  calc
    _ = u^2*(1/((36 : ℝ)^6*u^2)) := by field_simp [hu.ne']
    _ ≤ u^2*(E*(spectralABLExceptionalWindowReal 1 3 t/Real.cosh (Real.pi*t))) :=
      mul_le_mul_of_nonneg_left hW' (sq_nonneg _)
    _ = _ := by dsimp [u,E]; ring

theorem spectralABLOppositeFourierWeight_dominated (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖spectralABLOppositeFourierWeight f (t : ℂ)‖ ≤ C*‖spectralABLExceptionalCorrected 1 3 (t : ℂ)‖ := by
  obtain ⟨D,hD,hbound⟩ := spectralABLOppositeFourierWeight_normalized_rapid f hf hc hp 2
  refine ⟨(36 : ℝ)^6*D,by positivity,?_⟩
  intro t
  let Q := (1+t^2)^2*Real.exp (Real.pi*|t|)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  apply le_of_mul_le_mul_left _ hQ
  calc
    _ ≤ D := by
      simpa only [Q,Complex.ofReal_zero,zero_mul,add_zero] using hbound t 0 (by norm_num)
    _ = ((36 : ℝ)^6*D)*((36 : ℝ)^6)⁻¹ := by norm_num <;> ring
    _ ≤ ((36 : ℝ)^6*D)*(Q*‖spectralABLExceptionalCorrected 1 3 (t : ℂ)‖) :=
      mul_le_mul_of_nonneg_left (spectralABLExceptionalCorrected_one_three_lower t) (by positivity)
    _ = _ := by ring

theorem gamma0OppositeBareSpectrum_integrable (N : ℕ) [NeZero N] (r s : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    let h := spectralABLOppositeEnergyTest f hf hc hp
    Summable (fun i => ‖gamma0BareCuspidalTerm N h r s Y hY m n hm hn i‖) ∧
      IntegrableOn (gamma0BareContinuousRhoIntegrand N h r s Y hY m n hm hn) (Ioi (0 : ℝ)) := by
  let h := spectralABLOppositeEnergyTest f hf hc hp
  let h₀ := spectralABLExceptionalEnergyTest 1 3 (by norm_num)
  obtain ⟨C,hC,hdom⟩ := spectralABLOppositeFourierWeight_dominated f hf hc hp
  have hE (t : ℝ) : ‖spectralContinuousTestSymbol h t‖ ≤ C*‖spectralContinuousTestSymbol h₀ t‖ := by
    rw [show spectralContinuousTestSymbol h t = _ from
        spectralABLOppositeEnergyTest_continuous_symbol f hf hc hp t]
    have h₀eq : spectralContinuousTestSymbol h₀ t = spectralABLExceptionalCorrected 1 3 (t : ℂ) := by
      dsimp only [h₀]
      rw [spectralABLExceptionalEnergyTest_continuous_symbol,spectralABLExceptionalCorrected_real]
    rw [h₀eq]
    exact hdom t
  have hP (i : Gamma0HeatPrincipalCuspidalIndex N) :
      ‖gamma0CuspidalTestSymbol N h i.val‖ ≤ C*‖gamma0CuspidalTestSymbol N h₀ i.val‖ := by
    let l := gamma0AllHeightGradientSpectralValue N i.val
    let t := Real.sqrt (l-1/4)
    have ht : t^2 = l-1/4 := Real.sq_sqrt (sub_nonneg.mpr i.property)
    have he : spectralContinuousEnergyParameter t =
        ⟨l,gamma0AllHeightGradientSpectralValue_nonneg N i.val⟩ := by
      apply Subtype.ext
      change 1/4+t^2 = l
      rw [ht]
      ring
    unfold gamma0CuspidalTestSymbol
    change ‖h ⟨l,_⟩‖ ≤ C*‖h₀ ⟨l,_⟩‖
    rw [← he]
    exact hE t
  have h₀data := gamma0HeatExceptional_source_tendsto_bare N r s Y hY m n hm hn 1 3 (by norm_num)
  exact gamma0BareSpectrum_of_symbol_dominance N h h₀ r s Y hY m n hm hn C hC hP hE
    h₀data.1 h₀data.2.1

end
end ArtinMatthews
