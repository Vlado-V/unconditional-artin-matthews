module

public import ArtinMatthews.MarkedPhysicalActualIncidenceError


set_option backward.privateInPublic true
@[expose] public section

/-! Sum the proved per-class root errors over every actual ordered union
label and every actual special-linear residue. The original mass remains. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysicalActualUnion_modulus_bound {J : Type*} [Fintype J]
    (e : J → ℝ) {β x : ℝ} (hlog : 1 ≤ Real.log x) (heβ : ∀ j,e j ≤ β)
    (hβ : β+(1/100 : ℝ) ≤ 49/50)
    (u : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) (markedPadSlots x+1)) :
    (markedPhysicalMarkingProduct u : ℝ) ≤
      Real.exp ((8*(Fintype.card J : ℝ))*(Real.log x)^(49/50 : ℝ)) := by
  have hp := markedPadSlots_pow_le 1 hlog
  simp only [pow_one] at hp
  have h1 := Real.one_le_rpow hlog (by norm_num : (0 : ℝ)≤1/100)
  have hM : ((markedPadSlots x+1 : ℕ) : ℝ) ≤ 4*(Real.log x)^(1/100 : ℝ) := by
    push_cast
    nlinarith
  have hlogp : 0 < Real.log x := zero_lt_one.trans_le hlog
  have hK : 0 ≤ (Fintype.card J : ℝ) := Nat.cast_nonneg _
  apply (markedPhysicalMarking_product_bound e hlog heβ u).trans
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ 2*(Fintype.card J : ℝ)*(4*(Real.log x)^(1/100 : ℝ))*(Real.log x)^β := by gcongr
    _ = (8*(Fintype.card J : ℝ))*(Real.log x)^(β+1/100 : ℝ) := by
      rw [Real.rpow_add hlogp]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hlog hβ) (by positivity)

def markedPhysicalActualTotalRootError
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (x : ℝ)
    (hdis : Pairwise (fun i j => Disjoint (markedLogPowerBand (e i) x) (markedLogPowerBand (e j) x)))
    (d₀ Y U V A B C D R Q : ℝ) (ψ : ℝ → ℂ) : ℝ :=
  ∑ u : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) (markedPadSlots x+1),
    if hu : MarkedPhysicalMarkingDistinct u then
      let hP := fun j p (hp : p ∈ markedLogPowerBand (e j) x) => (mem_markedLogPowerBand.mp hp).1
      letI : NeZero (markedPhysicalMarkingProduct u) := ⟨(markedPhysicalMarkingProduct_pos hP u).ne'⟩
      let hS := markedPhysicalMarkingProduct_squarefree hP hdis u hu
      markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x+1) *
        ∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod (markedPhysicalMarkingProduct u)),
          |markedPhysicalActualIncidenceError e x u hS g d₀ Y U V A B C D R Q ψ|
    else 0

theorem markedPhysicalActualTotalRootError_bound
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10 : ℝ) ≤ e j) (β H R : ℝ)
    (hβ : 0 ≤ β) (heβ : ∀ j,e j ≤ β) (hβhi : β+(1/100 : ℝ)<49/50)
    (hH : 0 ≤ H) (hR : 0 ≤ R) {δ : ℝ} (hδ : 0 < δ) :
    ∃ E : ℝ, 0 < E ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (hdis : Pairwise (fun i j => Disjoint (markedLogPowerBand (e i) x) (markedLogPowerBand (e j) x)))
        (d₀ Y U V A B C D Q W : ℝ) (ψ : ℝ → ℂ),
        x^δ ≤ U → x^δ ≤ V → U ≤ A → A ≤ B → B ≤ 16*U →
        V ≤ C → C ≤ D → D ≤ 2*V →
        1 ≤ Q → Q ≤ Real.exp (H*(Real.log x)^(1/5 : ℝ)) →
        1 ≤ Y → Y ≤ Real.exp (H*(Real.log x)^(1/5 : ℝ)) →
        0 ≤ W → (∀ v,‖ψ v‖ ≤ W) →
        markedPhysicalActualTotalRootError e x hdis d₀ Y U V A B C D R Q ψ ≤
          (5*E*W)*x^(-δ/4000) := by
  have hβone : β+(1/100 : ℝ)<1 := hβhi.trans (by norm_num)
  obtain ⟨E,hE,herror⟩ := markedPhysicalActualIncidenceError_bound e he β H R hβ heβ hβone hH hR hδ
    (8*(Fintype.card J : ℝ))
  refine ⟨E,hE,?_⟩
  have hepos : ∀ j,0 < e j := fun j => by linarith [he j]
  have hband := eventually_all.mpr (fun j => marked_log_power_band_mass_eventually (hepos j))
  filter_upwards [herror, hband,
    markedPhysical_union_residue_mass_subpower e hepos β (δ/4000) hβ heβ hβone (by positivity),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_gt_atTop (0 : ℝ)] with x hx hV hbudget hlog hx0
  intro hdis d₀ Y U V A B C D Q W ψ hU hVscale hUA hAB hB hVC hCD hD hQ hQhi hY hYhi hW hψ
  let σ := markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x+1)
  let K := (5*E*W)*x^(-δ/2000)
  have hσ : 0 ≤ σ := markedPhysicalMass_nonneg _ _
    (fun j => ((by positivity : 0 < Real.log 2/2).trans (hV j).1).le)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  unfold markedPhysicalActualTotalRootError
  calc
    _ ≤ ∑ u : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) (markedPadSlots x+1),
      K*(if MarkedPhysicalMarkingDistinct u then σ*
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod (markedPhysicalMarkingProduct u))) : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro u _
      by_cases hu : MarkedPhysicalMarkingDistinct u
      · simp only [dite_eq_left hu,ite_eq_left hu]
        let hP := fun j p (hp : p ∈ markedLogPowerBand (e j) x) => (mem_markedLogPowerBand.mp hp).1
        let : NeZero (markedPhysicalMarkingProduct u) := ⟨(markedPhysicalMarkingProduct_pos hP u).ne'⟩
        have hs := markedPhysicalMarkingProduct_squarefree hP hdis u hu
        have hsum : (∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod (markedPhysicalMarkingProduct u)),
            |markedPhysicalActualIncidenceError e x u hs g d₀ Y U V A B C D R Q ψ|) ≤
            (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod (markedPhysicalMarkingProduct u))) : ℝ)*K := by
          calc
            _ ≤ ∑ _g : Matrix.SpecialLinearGroup (Fin 2) (ZMod (markedPhysicalMarkingProduct u)),K := by
              apply Finset.sum_le_sum
              intro g _
              exact hx u hs g d₀ Y U V A B C D Q W ψ hU hVscale
                (markedPhysicalActualUnion_modulus_bound e hlog heβ hβhi.le u)
                hUA hAB hB hVC hCD hD hQ hQhi hY hYhi hW hψ
            _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_eq_nat_card]
        apply (mul_le_mul_of_nonneg_left hsum hσ).trans_eq
        ring
      · simp only [dite_eq_right hu,ite_eq_right hu,mul_zero,le_refl]
    _ = K*∑ u : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) (markedPadSlots x+1),
      if MarkedPhysicalMarkingDistinct u then σ*
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod (markedPhysicalMarkingProduct u))) : ℝ) else 0 :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ K*x^(δ/4000) := mul_le_mul_of_nonneg_left hbudget hK
    _ = _ := by
      dsimp [K]
      rw [mul_assoc,← Real.rpow_add hx0]
      congr 2
      ring

end ArtinMatthews
