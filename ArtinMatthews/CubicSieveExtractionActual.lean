module

public import ArtinMatthews.CubicSieveExtractionRectangleActual
public import ArtinMatthews.CubicSievePrimeExtraction
public import ArtinMatthews.GiantSlotMellinIntegral
public import ArtinMatthews.PrimeExtractionDyadicLogGrowth
public import ArtinMatthews.PrimeExtractionLogMomentDecay


set_option backward.privateInPublic true
@[expose] public section

/-! The proved cubic box estimates, genuine Mellin integration and
the exact finite rough-to-prime reduction of section eight. -/
namespace ArtinMatthews
open Filter Finset MeasureTheory OAI.SevenEighths
open scoped BigOperators Asymptotics ContDiff FourierTransform SchwartzMap
noncomputable section

theorem cubicSieveExtractionBoxSaving_actual
    {J : Type} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (hinj : Function.Injective e)
    (he : ∀ j,(1/10:ℝ)<e j ∧ e j<(1/5:ℝ))
    (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,y^3=(A:OAI.CubicFirstMoment.Eisenstein))
    {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hs : Function.support Φ ⊆ Set.Icc 1 3)
    (γ : ℝ) (hγ : 0 < γ) {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4)
    (hdepth : 100*(5*(30:ℝ)+36)<(Fintype.card J:ℝ)) :
    CubicSieveExtractionBoxSaving e (cubicNumeratorHeckeCharacter A hA) χ Φ hΦ hs ε γ := by
  intro j hj
  let η := cubicNumeratorHeckeCharacter A hA
  let f : SchwartzMap ℝ ℂ := 𝓕 (primeExtractionRealLogProfile Φ zero_lt_one hs hΦ)
  let C := ∫ t : ℝ,‖f t‖
  let D := 1+2/Real.log 2
  have hC : 0 ≤ C := integral_nonneg (fun t => norm_nonneg (f t))
  let U := fun x => markedExtractionRelevantMellin e η χ (giantMarkedCenteredCore ε) Φ
    zero_lt_one hs hΦ γ j (Real.log x) x
  have hBig : U =O[atTop] (fun x : ℝ => x*(Real.log x)^2/(Real.log x)^5) := by
    apply Asymptotics.IsBigO.of_bound (C*3*D^2)
    filter_upwards [cubicSieve_extraction_rectangle_log_saving e hinj he A hA hnoncube χ γ hγ hε hεq hdepth,
      eventually_ge_atTop (1:ℝ),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 (Real.log 4)))]
      with x hrect hx hlog
    let L := Real.log x
    let N := ⌊3*x⌋₊
    let S := primeExtractionRelevantBoxes N 1 γ x
    let B (kl : ℕ×ℕ) := primeExtractionDyadicHeight kl.1 kl.2*L^(-(5:ℝ))
    have hL₁ : 1 ≤ L := (le_max_left _ _).trans hlog
    have hL := zero_lt_one.trans_le hL₁
    have hL₄ : Real.log ((3:ℝ)+1) ≤ L := by
      simpa only [show (3:ℝ)+1=4 by norm_num] using
        (le_max_right (1:ℝ) (Real.log 4)).trans hlog
    have hN : (N:ℝ) ≤ 3*x := Nat.floor_le (by positivity)
    have hB (kl : ℕ×ℕ) (_hkl : kl∈S) : 0 ≤ B kl := by
      dsimp only [B,primeExtractionDyadicHeight]
      positivity
    have hM : ‖U x‖ ≤ C*∑ kl ∈ S,B kl := by
      change ‖giantSlotMellinSum N S
        (markedExtractionBilinearCoefficient e η χ (giantMarkedCenteredCore ε) γ j x)
        f L x‖ ≤ _
      exact giant_slot_mellin_sum_norm_le N S _ f L x B hB
        (hrect j (mem_Icc.mp hj).2)
    have hbase : 0 ≤ 1+Real.log ((N:ℝ)+1)/Real.log 2 := by
      have hlogN := Real.log_nonneg (show 1 ≤ (N:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) N])
      positivity
    have hcard : (S.card:ℝ) ≤ (D*L)^2 := by
      calc
        _ ≤ ((primeExtractionDyadicActive N).card:ℝ) := Nat.cast_le.mpr
          (card_le_card (primeExtractionRelevantBoxes_subset _ _ _ _))
        _ ≤ (1+Real.log ((N:ℝ)+1)/Real.log 2)^2 := primeExtractionDyadicActive_count_le N
        _ ≤ _ := pow_le_pow_left₀ hbase
          (primeExtractionDyadicLogGrowth (by norm_num) hx hL₄ hL₁ hN) 2
    change ‖U x‖ ≤ (C*3*D^2)*‖x*L^2/L^5‖
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ x*L^2/L^5)]
    calc
      _ ≤ C*∑ kl ∈ S,B kl := hM
      _ ≤ C*∑ _kl ∈ S,(3*x)*L^(-(5:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply sum_le_sum
        intro kl hkl
        exact mul_le_mul_of_nonneg_right
          (primeExtractionRelevantBoxes_geometry hN hkl).2.1 (Real.rpow_nonneg hL.le _)
      _ = C*((S.card:ℝ)*((3*x)*L^(-(5:ℝ)))) := by simp only [sum_const,nsmul_eq_mul]
      _ ≤ C*((D*L)^2*((3*x)*L^(-(5:ℝ)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard (by positivity)) hC
      _ = _ := by
        rw [Real.rpow_neg hL.le,show (5:ℝ)=((5:ℕ):ℝ) from rfl,Real.rpow_natCast]
        ring
  exact hBig.trans_isLittleO (prime_extraction_log_moment_decay 1 (k:=5) (by norm_num))

theorem cubicSieve_rough_sub_prime_actual_isLittleO
    {J : Type} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (hinj : Function.Injective e)
    (he : ∀ j,(1/10:ℝ)<e j ∧ e j<(1/5:ℝ))
    (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,y^3=(A:OAI.CubicFirstMoment.Eisenstein))
    {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hs : Function.support Φ ⊆ Set.Icc 1 3)
    {γ ε : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1) (hε : 0 < ε) (hεq : ε < 1/4)
    (hdepth : 100*(5*(30:ℝ)+36)<(Fintype.card J:ℝ)) :
    (fun x => markedActualRoughThetaSum e (cubicNumeratorHeckeCharacter A hA) χ
      (giantMarkedCenteredCore ε) Φ 3 γ x -
      markedActualPrimeThetaSum e (cubicNumeratorHeckeCharacter A hA) χ
        (giantMarkedCenteredCore ε) Φ 3 x) =o[atTop]
          (fun x : ℝ => x*(Real.log x)^(-1:ℝ)) := by
  exact cubicSieve_rough_sub_prime_isLittleO e
    (fun j => ⟨(by norm_num : (0:ℝ)<1/10).trans (he j).1,(he j).2.le⟩)
    (cubicNumeratorHeckeCharacter A hA) χ hε hεq hγ hγ₁ Φ hΦ hs
    (cubicSieveExtractionBoxSaving_actual e hinj he A hA hnoncube χ Φ hΦ hs γ hγ hε hεq hdepth)

end
end ArtinMatthews
