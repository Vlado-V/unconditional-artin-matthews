module

public import ArtinMatthews.GiantSlotTypeIIRectangle
public import ArtinMatthews.GiantSlotMellinIntegral
public import ArtinMatthews.PrimeExtractionDyadicLogGrowth
public import ArtinMatthews.PrimeExtractionLogMomentDecay


set_option backward.privateInPublic true
@[expose] public section

/-! The actual unshifted ordinary slot discrepancy. The fixed Fourier
moment and the proved Type II estimate pay the full dyadic partition. -/

namespace ArtinMatthews
noncomputable section
open Filter Finset MeasureTheory
open scoped BigOperators Asymptotics ContDiff FourierTransform SchwartzMap Topology

theorem giant_unshifted_slot_isLittleO {J : Type} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (hinj : Function.Injective e)
    (he : ∀ j,(1/10:ℝ) < e j ∧ e j < (1/5:ℝ))
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (Φ : ℝ → ℝ) {a T : ℝ} (ha : 0 < a) (hT : 0 < T)
    (hsupp : Function.support Φ ⊆ Set.Icc a T) (hΦ : ContDiff ℝ ∞ Φ)
    (γ : ℝ) (hγ : 0 < γ) (C : ℕ) (hC : 2 ≤ C)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4)
    (hdepth : 100*(5*(29+2*(C:ℝ))+36) < (Fintype.card J:ℝ))
    (β : ℝ → ℕ → ℂ)
    (hβ : ∀ᶠ x : ℝ in atTop, (∀ n,‖β x n‖ ≤ (Real.log x)^C) ∧
      (∀ n,β x n≠0 → x^γ < (n:ℝ) ∧
        MarkedRoughAbove (Real.exp ((Real.log x)^(6/25:ℝ))) n)) :
    (fun x => giantSlotCutoffSum ⌊T*x⌋₊
      (giantOrdinarySlotCore e χ (giantMarkedCenteredCore ε) x γ (β x))
      (fun n => (Φ ((n:ℝ)/x):ℂ))) =o[atTop] (fun x : ℝ => x/Real.log x) := by
  let f : SchwartzMap ℝ ℂ := 𝓕 (primeExtractionRealLogProfile Φ ha hsupp hΦ)
  let D := 1+2/Real.log 2
  let V := (2/Real.log 2)^(Fintype.card J)
  let F₀ := ∫ t : ℝ,‖f t‖
  let F₁ := ∫ t : ℝ,|t|^(C+7)*‖f t‖
  let A (x : ℝ) := giantOrdinarySlotCore e χ (giantMarkedCenteredCore ε) x γ (β x)
  let U (x : ℝ) := giantSlotCutoffSum ⌊T*x⌋₊ (A x) (fun n => (Φ ((n:ℝ)/x):ℂ))
  have hF₀ : 0 ≤ F₀ := integral_nonneg (fun _ => norm_nonneg _)
  have hF₁ : 0 ≤ F₁ := integral_nonneg (fun _ => by positivity)
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hrect := giant_slot_mellin_rectangle_log_saving e hinj he χ a T γ (C:ℝ) 5
    hT hγ (by exact_mod_cast hC) (by norm_num) hε hεq (by linarith only [hdepth])
  have hcore := giantMarkedCenteredCore_interface e (fun j => (he j).2.trans (by norm_num)) hε hεq
  have hBig : U =O[atTop] (fun x : ℝ => x*(Real.log x)^2/(Real.log x)^5) := by
    apply Asymptotics.IsBigO.of_bound ((F₁*V+F₀)*T*D^2)
    filter_upwards [hrect,hcore,hβ,giant_centered_slot_norm_bound_eventually γ hγ,
      literalMarkedArrayWeight_bound_eventually e (fun j => (by norm_num : (0:ℝ)<1/10).trans (he j).1),
      eventually_ge_atTop (1:ℝ),Real.tendsto_log_atTop.eventually
        (eventually_ge_atTop (max 1 (Real.log (T+1))))] with x hr hF hb hα hw hx hlog
    let L := Real.log x
    let X := ⌊T*x⌋₊
    let S := primeExtractionRelevantBoxes X a γ x
    let M := giantSlotMellinSum X S (A x) f L x
    have hx₀ : 0 < x := zero_lt_one.trans_le hx
    have hL₁ : 1 ≤ L := (le_max_left _ _).trans hlog
    have hL : 0 < L := zero_lt_one.trans_le hL₁
    have hlogT : Real.log (T+1) ≤ L := (le_max_right _ _).trans hlog
    have hX : (X:ℝ) ≤ T*x := Nat.floor_le (mul_nonneg hT.le hx₀.le)
    have hA (m n : ℕ) : ‖A x m n‖ ≤ V*L^2*L^C := by
      have hh := giantOrdinarySlotCore_norm_le e χ (giantMarkedCenteredCore ε) x γ (β x)
        m n (hα m) (hb.1 n) (hw _) (hF.1 _)
      exact hh.trans_eq (by ring)
    have hU := giant_slot_cutoff_eq_relevant_dyads (A x) Φ hx₀ hsupp
      (fun m n hn => giantOrdinarySlotCore_support e χ (giantMarkedCenteredCore ε)
        x γ (β x) m n (fun n hn => (hb.2 n hn).1) hn)
    have hErr : ‖U x-M‖ ≤ (F₁/L^(C+7))*(V*L^2*L^C)*(X:ℝ)*
        (1+Real.log ((X:ℝ)+1)/Real.log 2)^2 := by
      change ‖giantSlotCutoffSum X (A x) (fun n => (Φ ((n:ℝ)/x):ℂ))-M‖ ≤ _
      rw [hU]
      exact prime_extraction_dyadic_subset_mellin_error (fun y => (Φ y:ℂ)) ha
        (primeExtraction_complexCutoff_support Φ hsupp) (Complex.ofRealCLM.contDiff.comp hΦ)
        X (A x) S (primeExtractionRelevantBoxes_subset _ _ _ _) (by positivity) hA (C+7) hL hx₀
    have hErr' : ‖U x-M‖ ≤ F₁*V*T*D^2*(x*L^2/L^5) := by
      calc
        _ ≤ (F₁/L^(C+7))*(V*L^2*L^C)*((X:ℝ)*(1+Real.log ((X:ℝ)+1)/Real.log 2)^2) := by
          simpa only [mul_assoc] using hErr
        _ ≤ (F₁/L^(C+7))*(V*L^2*L^C)*(T*D^2*x*L^2) :=
          mul_le_mul_of_nonneg_left (primeExtractionDyadicMassLogGrowth hT.le hx hlogT hL₁ hX)
            (by positivity)
        _ = _ := by
          rw [pow_add L C 7]
          field_simp [hL.ne']
    let B (kl : ℕ×ℕ) := primeExtractionDyadicHeight kl.1 kl.2*L^(-(5:ℝ))
    have hM : ‖M‖ ≤ F₀*∑ kl ∈ S,B kl := by
      apply giant_slot_mellin_sum_norm_le X S (A x) f L x B
      · intro kl _
        dsimp only [B,primeExtractionDyadicHeight]
        positivity
      · intro kl hkl t ht
        exact hr kl hkl (β x) (fun n => by simpa only [Real.rpow_natCast] using hb.1 n)
          (fun n hn => (hb.2 n hn).2) t ht
    have hbase : 0 ≤ 1+Real.log ((X:ℝ)+1)/Real.log 2 := by
      have hlogX : 0 ≤ Real.log ((X:ℝ)+1) :=
        Real.log_nonneg (by have h := Nat.cast_nonneg (α:=ℝ) X; linarith only [h])
      positivity
    have hcard : (S.card:ℝ) ≤ (D*L)^2 := by
      calc
        _ ≤ ((primeExtractionDyadicActive X).card:ℝ) := Nat.cast_le.mpr
          (card_le_card (primeExtractionRelevantBoxes_subset _ _ _ _))
        _ ≤ (1+Real.log ((X:ℝ)+1)/Real.log 2)^2 := primeExtractionDyadicActive_count_le X
        _ ≤ _ := pow_le_pow_left₀ hbase (primeExtractionDyadicLogGrowth hT.le hx hlogT hL₁ hX) 2
    have hM' : ‖M‖ ≤ F₀*T*D^2*(x*L^2/L^5) := by
      apply hM.trans
      calc
        _ ≤ F₀*∑ _kl ∈ S,(T*x)*L^(-(5:ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hF₀
          apply sum_le_sum
          intro kl hkl
          exact mul_le_mul_of_nonneg_right
            (primeExtractionRelevantBoxes_geometry hX hkl).2.1 (Real.rpow_nonneg hL.le _)
        _ = F₀*((S.card:ℝ)*((T*x)*L^(-(5:ℝ)))) := by simp only [sum_const,nsmul_eq_mul]
        _ ≤ F₀*((D*L)^2*((T*x)*L^(-(5:ℝ)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard (by positivity)) hF₀
        _ = _ := by
          rw [Real.rpow_neg hL.le,show (5:ℝ)=((5:ℕ):ℝ) from rfl,Real.rpow_natCast]
          ring
    change ‖U x‖ ≤ _*‖x*L^2/L^5‖
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ x*L^2/L^5)]
    calc
      _ ≤ ‖U x-M‖+‖M‖ := by simpa only [sub_add_cancel] using norm_add_le (U x-M) M
      _ ≤ F₁*V*T*D^2*(x*L^2/L^5)+F₀*T*D^2*(x*L^2/L^5) := add_le_add hErr' hM'
      _ = _ := by ring
  exact hBig.trans_isLittleO (by simpa only [Real.rpow_neg_one,div_eq_mul_inv] using
    prime_extraction_log_moment_decay 1 (k:=5) (by norm_num))

end
end ArtinMatthews
