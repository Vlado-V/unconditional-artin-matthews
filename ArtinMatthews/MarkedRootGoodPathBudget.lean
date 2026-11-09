module

public import ArtinMatthews.MarkedRootGoodPathReplacement
public import ArtinMatthews.MarkedRootGoodPathCost
public import ArtinMatthews.MarkedRootGridAbsorption


set_option backward.privateInPublic true
@[expose] public section

/-! The actual full path indicator replacement meets the growing-moment
precision with the source's c/8 grid. The root count and cut cost are proved. -/

noncomputable section
namespace ArtinMatthews
open Filter MeasureTheory
open scoped BigOperators

theorem markedRootGoodPath_replacement_log_budget {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (β : ℝ) (hβ : 0 ≤ β)
    (heβ : ∀ j,e j ≤ β) (hβhi : β+(1/100:ℝ)<1)
    {δ : ℝ} (hδ : 0 < δ) (Mr B C A : ℝ) (hB : 0 ≤ B) (hA : 0 ≤ A) :
    let α := max (β+1/100) (1/5:ℝ)
    ∀ᶠ x : ℝ in atTop,∀ {ι : Type*} (I : Finset ι)
      (source : ι → MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
      (S : ℕ) (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) (U V d₀ Y H : ℝ)
      (z w : ι → Fin 2 → ℝ),
      x^δ ≤ U → x^δ ≤ V → Squarefree S →
      (S:ℝ) ≤ Real.exp (Mr*(Real.log x)^(49/50:ℝ)) →
      Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y → Y ≤ Real.exp (B*(Real.log x)^(1/5:ℝ)) →
      0 ≤ H → H ≤ Real.exp (B*(Real.log x)^α) →
      (I.card:ℝ) ≤ Real.exp (B*(Real.log x)^α) →
      (∀ k ∈ I,markedVectorDet (z k) (w k)=1) →
      (∀ k ∈ I,∀ j,|z k j| ≤ H) → (∀ k ∈ I,∀ j,|w k j| ≤ H) →
      Real.exp (C*(Real.log x)^α)*
        (|(markedRootIndicatorCount g₀ U V (markedRootGoodPathSet e x I source d₀ Y U V z w):ℝ)-
          (U*V/((riemannZeta 2).re*(Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)):ℝ)))*
            markedNormalizedRootMeasure.real (markedRootGoodPathSet e x I source d₀ Y U V z w)|/(U*V)) ≤
        (Real.log x)^(-A*(markedMemoryMomentLength x:ℝ)) := by
  dsimp only
  let α : ℝ := max (β+1/100) (1/5)
  let D : ℝ := markedRootGoodPathCostExponent (Fintype.card J) B
  have hα : α<1 := max_lt hβhi (by norm_num)
  have hα0 : 0 ≤ α := le_trans (by norm_num) (le_max_right _ _)
  have hD : 0 ≤ D := by dsimp only [D,markedRootGoodPathCostExponent]; positivity
  have hc : 0 < δ/1000 := by positivity
  obtain ⟨E,hE,hroot⟩ := markedRootPartitionCountError_bound hδ Mr
  filter_upwards [hroot,markedRootArc_actual_widths_eventually e he,
    markedRootGrid_height_small α B (δ/1000) hα0 hα hc,
    markedRootGrid_actual_budget α D C (δ/1000) E (1/(riemannZeta 2).re) A hα0 hα hD hc hE.le
      (by positivity [markedRoot_zeta_two_pos]) hA,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),eventually_gt_atTop (1:ℝ)]
    with x hx hwidth hsmall hbudget hlog hx1
  intro ι I source S g₀ U V d₀ Y H z w hU hV hS hSr hY hYhi hH hHhi hI hdet hz hw
  let : NeZero S := ⟨hS.ne_zero⟩
  let N := markedRootGridSize (δ/1000) x
  let cost := markedRootGoodPathBoundaryCost e x I source d₀ Y H z w
  have hN : 0 < N := (markedRootGridSize_bounds hc hx1.le).1
  have hUp : 1 < U := (Real.one_lt_rpow hx1 hδ).trans_le hU
  have hVp : 1 < V := (Real.one_lt_rpow hx1 hδ).trans_le hV
  have hUV : 0 < U*V := mul_pos (by linarith) (by linarith)
  have hcost0 : 0 ≤ cost := markedRootGoodPathBoundaryCost_nonneg e x I source d₀ Y H z w hH
  have hY1 : 1 ≤ Y := (Real.one_le_exp (Real.rpow_nonneg (by linarith : 0 ≤ Real.log x) _)).trans hY
  have hcost : cost ≤ Real.exp (D*(Real.log x)^α) :=
    markedRootGoodPathCost_envelope e hβ hB (le_max_left _ _) (le_max_right _ _) hlog heβ
      I source d₀ Y H hY1 hYhi hH hHhi hI z w
  have hcmp := markedRootGoodPath_indicator_replacement e x I source d₀ Y U V H z w g₀ hUp hVp hH
    hdet hz hw ((hwidth.2 Y hY).2.le.trans (by norm_num))
    (fun j => (hwidth.1 j).2.le.trans (by norm_num)) N hN (hsmall H hH hHhi)
  have hs : (∑ i : MarkedRootGridIndex N,markedRootPartitionCountError g₀ U V N i)/(U*V) ≤
      E*15*(N:ℝ)^3*x^(-δ/1000) := by
    apply (div_le_iff₀ hUV).mpr
    calc
      _ ≤ ∑ _i : MarkedRootGridIndex N,E*U*V*x^(-δ/1000) :=
        Finset.sum_le_sum (fun i _ => hx S g₀ U V N hU hV hS hSr hN i)
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,markedRootGridIndex_card,Nat.cast_mul,
          Nat.cast_ofNat,Nat.cast_pow,nsmul_eq_mul]
        ring
  have hcard : 1 ≤ (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)):ℝ) := by
    exact_mod_cast (show 1 ≤ Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) from Nat.card_pos)
  have hden : 1/((riemannZeta 2).re*(Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)):ℝ)) ≤
      1/(riemannZeta 2).re := one_div_le_one_div_of_le markedRoot_zeta_two_pos
        (le_mul_of_one_le_right markedRoot_zeta_two_pos.le hcard)
  have hcmp' :
      |(markedRootIndicatorCount g₀ U V (markedRootGoodPathSet e x I source d₀ Y U V z w):ℝ)-
        (U*V/((riemannZeta 2).re*(Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)):ℝ)))*
          markedNormalizedRootMeasure.real (markedRootGoodPathSet e x I source d₀ Y U V z w)|/(U*V) ≤
      E*15*(N:ℝ)^3*x^(-δ/1000)+(1/(riemannZeta 2).re)*cost/(N:ℝ) := by
    apply (div_le_div_of_nonneg_right hcmp hUV.le).trans
    calc
      _ = (∑ i : MarkedRootGridIndex N,markedRootPartitionCountError g₀ U V N i)/(U*V)+
          (1/((riemannZeta 2).re*(Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)):ℝ)))*(cost/(N:ℝ)) := by
        dsimp only [cost]
        field_simp [hUV.ne']
      _ ≤ _ := add_le_add hs (by simpa only [mul_div_assoc] using
        mul_le_mul_of_nonneg_right hden (div_nonneg hcost0 (by positivity : 0 ≤ (N:ℝ))))
  apply (mul_le_mul_of_nonneg_left hcmp' (Real.exp_pos _).le).trans
  simpa only [neg_div] using hbudget cost hcost0 hcost

end ArtinMatthews
