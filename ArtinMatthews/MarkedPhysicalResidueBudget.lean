module

public import ArtinMatthews.MarkedPhysicalEndpointNorm
public import ArtinMatthews.MarkedRawRootArcGrowth
public import ArtinMatthews.FixedURootSLOrder


set_option backward.privateInPublic true
@[expose] public section

/-! Counting every actual ordered union label and every residue class still
costs only a subpower, with the original physical mass retained. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysicalMarking_card_bound {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) {β x : ℝ} (hlog : 1 ≤ Real.log x) (he : ∀ j,e j ≤ β) (M : ℕ) :
    (Fintype.card (MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) M) : ℝ) ≤
      Real.exp (2*(Fintype.card J : ℝ)*M*(Real.log x)^β) := by
  calc
    _ = ∏ j,∏ _k : Fin M,((markedLogPowerBand (e j) x).card : ℝ) := by
      simp [MarkedPhysicalMarking,Fintype.card_pi,Fintype.card_coe]
    _ ≤ ∏ _j : J,∏ _k : Fin M,Real.exp (2*(Real.log x)^β) := by
      apply Finset.prod_le_prod₀ (fun _ _ => Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))
      intro j _
      apply Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
      intro k _
      exact (markedBand_card_le_exp (e j) x).trans (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hlog (he j)) (by norm_num)))
    _ = _ := by simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← Real.exp_nat_mul]; congr 1; ring

theorem markedPhysicalMarking_product_bound {J : Type*} [Fintype J]
    (e : J → ℝ) {β x : ℝ} (hlog : 1 ≤ Real.log x) (he : ∀ j,e j ≤ β) {M : ℕ}
    (u : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) M) :
    (markedPhysicalMarkingProduct u : ℝ) ≤
      Real.exp (2*(Fintype.card J : ℝ)*M*(Real.log x)^β) := by
  calc
    _ = ∏ j,∏ k,(u j k : ℝ) := by simp [markedPhysicalMarkingProduct]
    _ ≤ ∏ _j : J,∏ _k : Fin M,Real.exp (2*(Real.log x)^β) := by
      apply Finset.prod_le_prod₀ (fun _ _ => Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))
      intro j _
      exact Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
        (fun k _ => markedRootArc_band_prime_le hlog (he j) (u j k).2)
    _ = _ := by simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← Real.exp_nat_mul]; congr 1; ring

theorem markedPhysical_SL_card_bound (S : ℕ) [NeZero S] :
    (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ) ≤ (S : ℝ)^4 := by
  have h := Fintype.card_le_of_injective
    (fun g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S) => (g : Matrix (Fin 2) (Fin 2) (ZMod S)))
    Subtype.val_injective
  have hc : Fintype.card (Matrix (Fin 2) (Fin 2) (ZMod S))=S^4 := by
    rw [Fintype.card_eq_nat_card]
    simp only [Matrix,Nat.card_fun,Nat.card_fin,Nat.card_zmod,← pow_mul]
  rw [hc] at h
  have hh : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) ≤ S^4 := by
    simpa only [Nat.card_eq_fintype_card] using h
  exact_mod_cast hh

theorem markedPhysical_union_residue_mass_subpower
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,0 < e j) (β η : ℝ)
    (hβ : 0 ≤ β) (heβ : ∀ j,e j ≤ β) (hβhi : β+(1/100 : ℝ)<1) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop,
      (∑ u : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) (markedPadSlots x+1),
        if MarkedPhysicalMarkingDistinct u then
          markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x+1) *
            (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod (markedPhysicalMarkingProduct u))) : ℝ)
        else 0) ≤ x^η := by
  let a := β+(1/100 : ℝ)
  let K : ℝ := Fintype.card J
  let c : ℝ := (Real.log 2/2)⁻¹
  have hc : 0 ≤ c := inv_nonneg.mpr (by positivity)
  have hK : 0 ≤ K := Nat.cast_nonneg _
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hb := eventually_all.mpr (fun j => marked_log_power_band_mass_eventually (he j))
  filter_upwards [hb,Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    marked_sublinear_log_exp_le_rpow_eventually a ((40+4*c)*K) η hβhi hη] with x hV hlog hpower
  let M := markedPadSlots x+1
  let t := (Real.log x)^a
  have ht : 0 ≤ t := Real.rpow_nonneg (zero_le_one.trans hlog) _
  have hlogp : 0 < Real.log x := zero_lt_one.trans_le hlog
  have hM : (M : ℝ) ≤ 4*(Real.log x)^(1/100 : ℝ) := by
    have hm := markedPadSlots_pow_le 1 hlog
    simp only [pow_one] at hm
    have h1 := Real.one_le_rpow hlog (by norm_num : (0 : ℝ)≤1/100)
    dsimp [M]
    push_cast
    nlinarith
  have hMt : (M : ℝ) ≤ 4*t := hM.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hlog (by dsimp [a]; linarith)) (by norm_num))
  have hMβ : (M : ℝ)*(Real.log x)^β ≤ 4*t := by
    apply (mul_le_mul_of_nonneg_right hM (Real.rpow_nonneg hlogp.le _)).trans_eq
    dsimp [t,a]
    rw [mul_assoc,← Real.rpow_add hlogp]
    congr 2
    ring
  have hex : 2*K*M*(Real.log x)^β ≤ 8*K*t := by nlinarith [mul_le_mul_of_nonneg_left hMβ hK]
  have hlabels : (Fintype.card (MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) M) : ℝ) ≤
      Real.exp (8*K*t) := (markedPhysicalMarking_card_bound e hlog heβ M).trans (Real.exp_le_exp.mpr hex)
  have hσ : 0 ≤ markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) M :=
    markedPhysicalMass_nonneg _ M (fun j => (by positivity : 0 < Real.log 2/2).le.trans (hV j).1.le)
  have hmass : markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) M ≤
      Real.exp (4*c*K*t) := by
    calc
      _ ≤ ∏ _j : J,(Real.exp c)^M := by
        apply Finset.prod_le_prod₀ (fun j _ => pow_nonneg (inv_nonneg.mpr
          ((by positivity : 0 < Real.log 2/2).le.trans (hV j).1.le)) M)
        intro j _
        apply pow_le_pow_left₀ (inv_nonneg.mpr ((by positivity : 0 < Real.log 2/2).le.trans (hV j).1.le))
        have hinv : (bandReciprocalMass (markedLogPowerBand (e j) x))⁻¹ ≤ c := by
          simpa only [c,one_div,bandReciprocalMass] using
            (one_div_le_one_div_of_le (by positivity : 0 < Real.log 2/2) (hV j).1.le)
        exact hinv.trans (by linarith [Real.add_one_le_exp c])
      _ = Real.exp (c*M*K) := by simp only [Finset.prod_const,Finset.card_univ,← Real.exp_nat_mul]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hMt (mul_nonneg hc hK)])
  have hres (u : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) M) :
      (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod (markedPhysicalMarkingProduct u))) : ℝ) ≤
        Real.exp (32*K*t) := by
    have hp := markedPhysicalMarkingProduct_pos (fun j p hp => (mem_markedLogPowerBand.mp hp).1) u
    let : NeZero (markedPhysicalMarkingProduct u) := ⟨hp.ne'⟩
    calc
      _ ≤ (markedPhysicalMarkingProduct u : ℝ)^4 := markedPhysical_SL_card_bound _
      _ ≤ (Real.exp (8*K*t))^4 := pow_le_pow_left₀ (Nat.cast_nonneg _)
        ((markedPhysicalMarking_product_bound e hlog heβ u).trans (Real.exp_le_exp.mpr hex)) 4
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  calc
    _ ≤ ∑ _u : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) M,
        Real.exp (4*c*K*t)*Real.exp (32*K*t) := by
      apply Finset.sum_le_sum
      intro u _
      split_ifs
      · exact mul_le_mul hmass (hres u) (Nat.cast_nonneg _) (Real.exp_pos _).le
      · positivity
    _ = (Fintype.card (MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) M) : ℝ)*
        (Real.exp (4*c*K*t)*Real.exp (32*K*t)) := by simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ]
    _ ≤ Real.exp (8*K*t)*(Real.exp (4*c*K*t)*Real.exp (32*K*t)) :=
      mul_le_mul_of_nonneg_right hlabels (by positivity)
    _ = Real.exp (((40+4*c)*K)*(Real.log x)^a) := by
      rw [← Real.exp_add,← Real.exp_add]
      congr 1
      dsimp [t]
      ring
    _ ≤ _ := hpower

end ArtinMatthews
