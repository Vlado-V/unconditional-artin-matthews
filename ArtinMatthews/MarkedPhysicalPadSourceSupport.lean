module

public import ArtinMatthews.MarkedPhysicalHarmonicScalar
public import ArtinMatthews.MarkedMajorTypeIISupportedCoefficient


set_option backward.privateInPublic true
@[expose] public section

/-! Actual band, determinant cutoff and cofactor support for the
harmonic-to-scalar identity, at the original rough cutoff. -/
namespace ArtinMatthews
open Filter
noncomputable section

theorem markedPhysicalPadSource_cutoffs {J : Type*}
    (e : J → ℝ) (he : ∀ j,e j ≤ (1/5:ℝ)) (B R : ℝ) (hR : 0 ≤ R) :
    ∀ᶠ x : ℝ in atTop,∀ Y : ℝ,0 < Y → Y ≤ Real.exp (B*(Real.log x)^(1/5:ℝ)) →
      (∀ j p,p ∈ markedLogPowerBand (e j) x → (p:ℝ) < Real.exp ((Real.log x)^(6/25:ℝ))) ∧
      R*Y < Real.exp ((Real.log x)^(6/25:ℝ)) := by
  let C := max 3 (R+B+1)
  have hpow := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/25)).comp Real.tendsto_log_atTop
  filter_upwards [hpow.eventually (eventually_ge_atTop C),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hc hx
  intro Y hY hYmax
  let L := Real.log x
  have hLp : 0 < L := zero_lt_one.trans_le hx
  have hLo : 1 ≤ L^(1/5:ℝ) := Real.one_le_rpow hx (by norm_num)
  have hC : C*L^(1/5:ℝ) ≤ L^(6/25:ℝ) := by
    calc
      _ ≤ L^(1/25:ℝ)*L^(1/5:ℝ) :=
        mul_le_mul_of_nonneg_right hc (zero_le_one.trans hLo)
      _ = _ := by rw [← Real.rpow_add hLp]; norm_num
  constructor
  · intro j p hp
    have h₂ : (2:ℝ)*L^(1/5:ℝ) < C*L^(1/5:ℝ) :=
      mul_lt_mul_of_pos_right ((by norm_num : (2:ℝ)<3).trans_le (le_max_left _ _))
        (zero_lt_one.trans_le hLo)
    exact (mem_markedLogPowerBand.mp hp).2.2.trans_lt (Real.exp_lt_exp.mpr
      ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (he j)) (by norm_num)).trans_lt
        (h₂.trans_le hC)))
  · have hRe : R ≤ Real.exp R := by linarith [Real.add_one_le_exp R]
    have hE : R+B*L^(1/5:ℝ) < C*L^(1/5:ℝ) := by
      calc
        _ ≤ (R+B)*L^(1/5:ℝ) := by nlinarith [mul_nonneg hR (sub_nonneg.mpr hLo)]
        _ < _ := mul_lt_mul_of_pos_right ((lt_add_one (R+B)).trans_le (le_max_right _ _))
          (zero_lt_one.trans_le hLo)
    calc
      _ ≤ Real.exp R*Real.exp (B*L^(1/5:ℝ)) :=
        mul_le_mul hRe hYmax hY.le (Real.exp_nonneg _)
      _ = Real.exp (R+B*L^(1/5:ℝ)) := (Real.exp_add _ _).symm
      _ < _ := Real.exp_lt_exp.mpr (hE.trans_le hC)

theorem markedPhysicalPadSource_harmonic_eq_survival
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    (hinj : Function.Injective e) (δ B R : ℝ) (hδ : 0 < δ) (hR : 0 ≤ R)
    (η : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ)
    (hη : Function.support η ⊆ Set.Icc 1 4) (hψ : Function.support ψ ⊆ Set.Icc (-R) R) :
    ∀ᶠ x : ℝ in atTop,∀ (Y Hm Hn Q : ℝ),0 < Y → Y ≤ Real.exp (B*(Real.log x)^(1/5:ℝ)) →
      x^δ ≤ Hm → x^δ ≤ Hn →
      ∀ (S T : Finset ℕ) (modulation : ℝ) (β ξ : ℕ → ℂ),
      (∀ m∈S,Hm ≤ (m:ℝ) ∧ (m:ℝ) ≤ 2*Hm) →
      (∀ n∈T,Hn ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*Hn) →
      (∀ n∈T,β n ≠ 0 → ∀ p ∈ Nat.primesLE ⌊Real.exp ((Real.log x)^(6/25:ℝ))⌋₊,¬p∣n) →
      let P := fun j => markedLogPowerBand (e j) x
      let M := ⌊(Real.log x)^(1/100:ℝ)⌋₊
      let Z := markedPhysicalTypeIIDyadBox Y Hm Hn
      let W := Real.exp ((Real.log x)^(6/25:ℝ))
      let α' := fun n => ξ n*markedMajorRestrictedCoefficient W modulation S n
      let β' := fun n => ξ n*markedPhysicalRestrictedBeta T β n
      (markedPhysicalHarmonicPaddedDetectorSum P M Z η Y (markedRawEdgeDeltaDetector ψ Y) α' β' =
        markedPhysicalPadSurvivalScalarSum P M S T η Y (markedRawEdgeDeltaDetector ψ Y) α' β') ∧
      (markedPhysicalHarmonicPaddedDetectorSum P M Z η Y (markedRawEdgeMajorDetector ψ Q Y) α' β' =
        markedPhysicalPadSurvivalScalarSum P M S T η Y (markedRawEdgeMajorDetector ψ Q Y) α' β') := by
  have hbands := eventually_all.mpr (fun j => marked_log_power_band_mass_eventually
    ((by norm_num : (0:ℝ)<1/10).trans_le (he j)))
  filter_upwards [markedPhysicalPadSource_cutoffs e heUpper B R hR, hbands,
    marked_array_disjoint_eventually e hinj, eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (markedMajorTypeII_supported_alpha δ hδ)]
    with x hcut hmass hdis hx hα₀
  intro Y Hm Hn Q hY hYhi hHm hHn S T modulation β ξ hS hT hβ
  dsimp only
  let W := Real.exp ((Real.log x)^(6/25:ℝ))
  have hx₀ := zero_lt_one.trans hx
  have hxδ := Real.rpow_pos_of_pos hx₀ δ
  have hV j : 0 < bandReciprocalMass (markedLogPowerBand (e j) x) := by
    have h := (hmass j).1
    exact lt_of_lt_of_le (by positivity : 0 < Real.log 2/2) h.le
  have hsmall := markedPhysical_delta_major_small_support ψ hY hψ (hcut Y hY hYhi).2 Q
  have heq : Real.exp (δ*Real.log x) = x^δ := by
    rw [Real.rpow_def_of_pos hx₀,mul_comm]
  have hα₁ := (hα₀ S modulation (fun m hm => heq.trans_le (hHm.trans (hS m hm).1))).2
  have hα' (m : ℕ) (hm : ξ m*markedMajorRestrictedCoefficient W modulation S m ≠ 0) :
      m ∈ S ∧ MarkedPhysicalRoughAt W m := by
    have h0 := (mul_ne_zero_iff.mp hm).2
    exact ⟨((markedMajorRestrictedCoefficient_nonzero W modulation S m).mp h0).1,
      markedPhysicalRoughAt_of_avoids (Real.exp_nonneg _) (hα₁ m h0)⟩
  have hβ' (n : ℕ) (hn : ξ n*markedPhysicalRestrictedBeta T β n ≠ 0) :
      n ∈ T ∧ MarkedPhysicalRoughAt W n := by
    have h0 := (mul_ne_zero_iff.mp hn).2
    have hTn : n ∈ T := by
      by_contra hne
      simp only [markedPhysicalRestrictedBeta,ite_eq_right hne,ne_eq,not_true_eq_false] at h0
    have hβn : β n ≠ 0 := by
      simpa only [markedPhysicalRestrictedBeta,ite_eq_left hTn] using h0
    exact ⟨hTn,markedPhysicalRoughAt_of_avoids (Real.exp_nonneg _) (hβ n hTn hβn)⟩
  constructor
  · exact markedPhysicalHarmonicPaddedDetectorSum_eq_survival_scalar _
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) hdis hV _
      hY (hxδ.trans_le hHm).le (hxδ.trans_le hHn).le (hcut Y hY hYhi).1 hη hsmall.1 S T hS hT hα' hβ'
  · exact markedPhysicalHarmonicPaddedDetectorSum_eq_survival_scalar _
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) hdis hV _
      hY (hxδ.trans_le hHm).le (hxδ.trans_le hHn).le (hcut Y hY hYhi).1 hη hsmall.2 S T hS hT hα' hβ'

end
end ArtinMatthews
