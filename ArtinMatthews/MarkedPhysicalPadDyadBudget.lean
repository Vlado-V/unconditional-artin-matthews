module

public import ArtinMatthews.MarkedPhysicalPadHarmonic
public import ArtinMatthews.MarkedPhysicalResidueBudget
public import ArtinMatthews.MarkedMajorPrimeDyads


set_option backward.privateInPublic true
@[expose] public section

/-! Actual auxiliary-pad dyad budgets at the source hierarchy. No pad
product, dyad-count or logarithmic-scale estimate is a hypothesis. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]
  (e : J → ℝ) {x : ℝ} (hlog : 1≤Real.log x) (he : ∀ j,e j≤(1/5:ℝ))

include hlog he

omit [DecidableEq J] in
theorem markedPhysicalActualPadProduct_bound
    (c : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) ⌊(Real.log x)^(1/100:ℝ)⌋₊) :
    (markedPhysicalMarkingProduct c:ℝ)≤
      Real.exp (2*(Fintype.card J:ℝ)*(Real.log x)^(21/100:ℝ)) := by
  have hL : 0<Real.log x := zero_lt_one.trans_le hlog
  apply (markedPhysicalMarking_product_bound e hlog he c).trans
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ 2*(Fintype.card J:ℝ)*(Real.log x)^(1/100:ℝ)*(Real.log x)^(1/5:ℝ) := by
      gcongr
      exact Nat.floor_le (Real.rpow_nonneg hL.le _)
    _ = _ := by rw [mul_assoc,← Real.rpow_add hL]; norm_num

theorem markedPhysicalActualPadDyad_card :
    ((markedPhysicalPadDyadIndices (fun j => markedLogPowerBand (e j) x)
      ⌊(Real.log x)^(1/100:ℝ)⌋₊).card:ℝ)≤
      (1+2*(Fintype.card J:ℝ)/Real.log 2)*Real.log x := by
  let P := fun j => markedLogPowerBand (e j) x
  let M := ⌊(Real.log x)^(1/100:ℝ)⌋₊
  let A := 2*(Fintype.card J:ℝ)*(Real.log x)^(21/100:ℝ)
  let S := Finset.univ.image (fun c : MarkedPhysicalMarking P M => markedPhysicalMarkingProduct c)
  have hA : 0≤A := by dsimp [A]; positivity
  have hS : ∀ D∈S,(D:ℝ)≤Real.exp A := by
    intro D hD
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hD
    exact markedPhysicalActualPadProduct_bound e hlog he c
  have hcount := markedMajorPrimeDyadIndices_card S (Real.exp A)
    (by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hA) hS
  have hi : markedPhysicalPadDyadIndices P M=markedMajorPrimeDyadIndices S := by
    simp only [markedPhysicalPadDyadIndices,markedMajorPrimeDyadIndices,S,Finset.image_image]
    rfl
  change ((markedPhysicalPadDyadIndices P M).card:ℝ)≤_
  rw [hi]
  apply hcount.trans
  rw [Real.log_exp]
  have hp : (Real.log x)^(21/100:ℝ)≤Real.log x := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hlog (by norm_num : (21/100:ℝ)≤1)
  have hc : 0≤2*(Fintype.card J:ℝ)/Real.log 2 := by positivity
  have hh := mul_le_mul_of_nonneg_left hp hc
  calc
    _ = 1+(2*(Fintype.card J:ℝ)/Real.log 2)*(Real.log x)^(21/100:ℝ) := by dsimp [A]; ring
    _ ≤ Real.log x+(2*(Fintype.card J:ℝ)/Real.log 2)*Real.log x := add_le_add hlog hh
    _ = _ := by ring

theorem markedPhysicalActualPadDyad_scale
    (j : ℕ) (hj : j∈markedPhysicalPadDyadIndices (fun i => markedLogPowerBand (e i) x)
      ⌊(Real.log x)^(1/100:ℝ)⌋₊) :
    1≤((2:ℕ)^j:ℝ) ∧
      ((2:ℕ)^j:ℝ)≤Real.exp (2*(Fintype.card J:ℝ)*(Real.log x)^(21/100:ℝ)) ∧
      Real.log (2*((2:ℕ)^j:ℝ))≤(2*(Fintype.card J:ℝ)+1)*(Real.log x)^(21/100:ℝ) := by
  obtain ⟨c,_,hc⟩ := Finset.mem_image.mp hj
  have hd := (markedPhysicalPad_dyad_iff (fun i => markedLogPowerBand (e i) x)
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) _ c j).mpr hc
  have hp : 0<((2:ℕ)^j:ℝ) := by positivity
  have hbound := hd.1.trans (markedPhysicalActualPadProduct_bound e hlog he c)
  refine ⟨by exact_mod_cast (Nat.one_le_pow j 2 (by norm_num)),hbound,?_⟩
  have hl := (Real.log_le_iff_le_exp hp).mpr hbound
  have hlog2 : Real.log 2≤(1:ℝ) := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hpow : 1≤(Real.log x)^(21/100:ℝ) := Real.one_le_rpow hlog (by norm_num)
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hp.ne']
  nlinarith

theorem markedPhysicalActualPadDyad_Y_bound
    (B Y : ℝ) (hB : 0≤B) (hY0 : 0≤Y)
    (hY : Y≤Real.exp (B*(Real.log x)^(1/5:ℝ)))
    (j : ℕ) (hj : j∈markedPhysicalPadDyadIndices (fun i => markedLogPowerBand (e i) x)
      ⌊(Real.log x)^(1/100:ℝ)⌋₊) :
    ((2:ℕ)^j:ℝ)*Y≤Real.exp ((2*(Fintype.card J:ℝ)+B)*(Real.log x)^(21/100:ℝ)) := by
  have hd := (markedPhysicalActualPadDyad_scale e hlog he j hj).2.1
  calc
    _ ≤ Real.exp (2*(Fintype.card J:ℝ)*(Real.log x)^(21/100:ℝ))*
        Real.exp (B*(Real.log x)^(1/5:ℝ)) := mul_le_mul hd hY hY0 (Real.exp_nonneg _)
    _ = Real.exp (2*(Fintype.card J:ℝ)*(Real.log x)^(21/100:ℝ)+
        B*(Real.log x)^(1/5:ℝ)) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have hh := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hlog (by norm_num : (1/5:ℝ)≤21/100)) hB
      nlinarith)

end
end ArtinMatthews
