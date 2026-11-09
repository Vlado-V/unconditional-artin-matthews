module

public import ArtinMatthews.MarkedTypeIICommonQuotientBound
public import ArtinMatthews.MarkedTypeIILabelDyadBudget
public import ArtinMatthews.MarkedMajorTypeIICoefficients


set_option backward.privateInPublic true
@[expose] public section

/-! The original marking bands and centered dyadic coefficients give
arbitrary fixed logarithmic saving for the common-quotient collision. -/

namespace ArtinMatthews
noncomputable section
open Filter Finset
open scoped BigOperators Topology

variable {J : Type*} [Fintype J]

theorem markedTypeII_actual_label_fourth_le_eventually
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, ∀ X : ℕ, x^δ ≤ (X:ℝ) →
      ∀ a ∈ markedMajorLabelSet (fun j => markedLogPowerBand (e j) x), a^4 ≤ X := by
  let K := (Fintype.card J:ℝ)
  have ht := (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 4/5)).comp Real.tendsto_log_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop (8*K/δ)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    eventually_gt_atTop (0:ℝ)] with x hg hlog hx
  intro X hX a ha
  let L := Real.log x
  have hL : 0 < L := zero_lt_one.trans_le hlog
  change 8*K/δ ≤ L^(4/5:ℝ) at hg
  have hs : (4:ℝ)*(2*K*L^(1/5:ℝ)) ≤ δ*L := by
    calc
      _ = (8*K)*L^(1/5:ℝ) := by ring
      _ ≤ (L^(4/5:ℝ)*δ)*L^(1/5:ℝ) :=
        mul_le_mul_of_nonneg_right ((div_le_iff₀ hδ).mp hg) (Real.rpow_nonneg hL.le _)
      _ = _ := by
        rw [mul_comm (L^(4/5:ℝ)) δ,mul_assoc,← Real.rpow_add hL]
        norm_num
  have hau := (markedTypeII_actual_label_product_bounds e hlog he heUpper ha).2
  have hfour : (a:ℝ)^4 ≤ (X:ℝ) := calc
    _ ≤ (Real.exp (2*K*L^(1/5:ℝ)))^4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hau 4
    _ = Real.exp ((4:ℝ)*(2*K*L^(1/5:ℝ))) := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ Real.exp (δ*L) := Real.exp_le_exp.mpr hs
    _ = x^δ := by rw [Real.rpow_def_of_pos hx,mul_comm δ L]
    _ ≤ _ := hX
  exact_mod_cast hfour

theorem markedTypeII_dyad_collision_log_saving
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    (δ Cbox Cα Cβ G : ℝ) (hδ : 0 < δ) (hbox : 0 < Cbox)
    (η : ℝ → ℂ) (hη : ∀ u, ‖η u‖ ≤ 1) (hsupp : Function.support η ⊆ Set.Icc 1 4) :
    ∀ᶠ x : ℝ in atTop, ∀ Y : ℝ, 0 < Y →
      ∀ (M N H : Finset ℕ) (X : ℕ), x^δ ≤ (X:ℝ) → (X:ℝ) ≤ Cbox*x →
      (∀ v ∈ M×ˢN,v.1*v.2 ≤ X) →
      ∀ α β : ℕ → ℂ, (∀ m ∈ M, ‖α m‖ ≤ (Real.log x)^Cα) →
      (∀ n ∈ N, ‖β n‖ ≤ (Real.log x)^Cβ) →
      let P := fun j => markedLogPowerBand (e j) x
      ‖markedTypeIICollisionSum (giantMarkedEndpoints P M N) H
        (markedTypeIIDyadCoefficient P η Y α β)‖ ≤ Y*(X:ℝ)*(Real.log x)^(-G) := by
  let Vmax := ((Real.log 2/2)⁻¹)^(Fintype.card J)
  let E := 2*(Cα+Cβ)+3
  let C := 128*Vmax^2*(Cbox+1)^3
  have hV₀ : 0 < Real.log 2/2 := by positivity
  have hbands := eventually_all.mpr (fun j => marked_log_power_band_mass_eventually
    ((by norm_num : (0:ℝ) < 1/10).trans_le (he j)))
  have hdecay := (marked_bands_reciprocal_square_log_saving Finset.univ e
    (fun j _ => he j) (G+E)).const_mul C
  simp only [mul_zero] at hdecay
  have hsmall := ((tendsto_order.1 hdecay).2 1 zero_lt_one).mono (fun _ hx => hx.le)
  filter_upwards [hbands,markedTypeII_actual_label_fourth_le_eventually e he heUpper δ hδ,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    eventually_gt_atTop (0:ℝ),hsmall] with x hxV hlabel hlog hx hs
  intro Y hY M N H X hX₁ hX₂ hMN α β hα hβ
  dsimp only
  let L := Real.log x
  let P := fun j => markedLogPowerBand (e j) x
  let m := ∑ p ∈ Finset.univ.biUnion P, 1/(p:ℝ)^2
  have hL : 0 < L := zero_lt_one.trans_le hlog
  have hm : 0 ≤ m := sum_nonneg (fun _ _ => by positivity)
  have hVp (j : J) : 0 < bandReciprocalMass (P j) := hV₀.trans (hxV j).1
  have hV : 0 ≤ markedMajorLabelMass P := (markedMajorLabelMass_pos P hVp).le
  have hVmax : markedMajorLabelMass P ≤ Vmax := by
    unfold markedMajorLabelMass
    have hprod := prod_le_prod₀
      (s := (Finset.univ : Finset J)) (f := fun j => (bandReciprocalMass (P j))⁻¹)
      (g := fun _ => (Real.log 2/2)⁻¹)
      (fun j _ => inv_nonneg.mpr (hVp j).le)
      (fun j _ => inv_anti₀ hV₀ (hxV j).1.le)
    simpa only [prod_const,card_univ,Vmax] using hprod
  have hX : 0 < (X:ℝ) := (Real.rpow_pos_of_pos hx δ).trans_le hX₁
  have hlogX : 1+Real.log (X:ℝ) ≤ (Cbox+1)*L := by
    have hh := Real.log_le_log hX hX₂
    rw [Real.log_mul hbox.ne' hx.ne'] at hh
    change 1 ≤ L at hlog
    nlinarith [Real.log_le_sub_one_of_pos hbox,
      mul_nonneg hbox.le (sub_nonneg.mpr hlog)]
  have hpow : (L^Cα*L^Cβ)^2*L^3 = L^E := by
    rw [← Real.rpow_add hL,← Real.rpow_mul_natCast hL.le,← Real.rpow_natCast L 3,
      ← Real.rpow_add hL]
    congr 1
    dsimp only [E]
    push_cast
    ring
  have hsave : C*L^E*m ≤ L^(-G) := by
    change C*(L^(G+E)*m) ≤ 1 at hs
    rw [Real.rpow_neg hL.le,← one_div]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hL G)).mpr
    calc
      _ = C*(L^(G+E)*m) := by rw [Real.rpow_add hL G E]; ring
      _ ≤ 1 := hs
  calc
    _ ≤ 128*(markedMajorLabelMass P)^2*(L^Cα*L^Cβ)^2*Y*(X:ℝ)*(1+Real.log (X:ℝ))^3*m :=
      markedTypeII_dyad_collision_norm_le P (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
        M N H X hMN η hY hη hsupp (fun a ha => hlabel X hX₁ a (mem_filter.mp ha).1)
        α β (Real.rpow_nonneg hL.le _) (Real.rpow_nonneg hL.le _) hα hβ
    _ ≤ 128*Vmax^2*(L^Cα*L^Cβ)^2*Y*(X:ℝ)*((Cbox+1)*L)^3*m := by
      gcongr
    _ = Y*(X:ℝ)*(C*((L^Cα*L^Cβ)^2*L^3)*m) := by dsimp only [C]; ring
    _ = Y*(X:ℝ)*(C*L^E*m) := by rw [hpow]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsave (mul_nonneg hY.le hX.le)

theorem markedTypeII_actual_dyad_collision_log_saving
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    (δ Cbox Cβ G : ℝ) (hδ : 0 < δ) (hbox : 0 < Cbox) :
    ∀ᶠ x : ℝ in atTop, ∀ Y : ℝ, 0 < Y →
      ∀ (M N H : Finset ℕ) (X : ℕ), x^δ ≤ (X:ℝ) → (X:ℝ) ≤ Cbox*x →
      (∀ v ∈ M×ˢN,v.1*v.2 ≤ X) → (∀ m ∈ M, x^δ ≤ (m:ℝ)) →
      ∀ (modulation : ℝ) (β : ℕ → ℂ), (∀ n ∈ N, ‖β n‖ ≤ (Real.log x)^Cβ) →
      let P := fun j => markedLogPowerBand (e j) x
      let α := markedMajorCenteredCoefficient (Real.exp ((Real.log x)^(6/25:ℝ))) modulation
      ‖markedTypeIICollisionSum (giantMarkedEndpoints P M N) H
        (markedTypeIIDyadCoefficient P markedTypeIILabelCutoff Y α β)‖ ≤
          Y*(X:ℝ)*(Real.log x)^(-G) := by
  filter_upwards [markedTypeII_dyad_collision_log_saving e he heUpper δ Cbox 2 Cβ G hδ hbox
    markedTypeIILabelCutoff markedTypeIILabelCutoff_norm_le_one markedTypeIILabelCutoff_support,
    Real.tendsto_log_atTop.eventually (markedMajorTypeII_alpha_bound δ hδ),
    eventually_gt_atTop (0:ℝ)] with x hsave hα hx
  intro Y hY M N H X hX₁ hX₂ hMN hM modulation β hβ
  dsimp only
  apply hsave Y hY M N H X hX₁ hX₂ hMN _ β _ hβ
  intro m hm
  have heq : Real.exp (δ*Real.log x) = x^δ := by rw [Real.rpow_def_of_pos hx,mul_comm]
  have h := hα m modulation (heq.symm ▸ hM m hm)
  rw [show (2:ℝ) = ((2:ℕ):ℝ) from rfl, Real.rpow_natCast]
  exact h

end
end ArtinMatthews
