module

public import ArtinMatthews.MarkedTypeIILabelDyads
public import ArtinMatthews.MarkedTypeIICollisionDecay


set_option backward.privateInPublic true
@[expose] public section

/-! The actual one-prime-per-band labels give the source Y range and
the actual number of occupied smooth label dyads. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators Classical
noncomputable section

theorem markedTypeII_actual_label_product_bounds {J : Type*} [Fintype J]
    (e : J → ℝ) {x : ℝ} (hlog : 1≤Real.log x)
    (he : ∀ j,(1/10:ℝ)≤e j) (heUpper : ∀ j,e j≤(1/5:ℝ))
    {b : ℕ} (hb : b∈markedMajorLabelSet (fun j => markedLogPowerBand (e j) x)) :
    Real.exp ((Fintype.card J:ℝ)*(Real.log x)^(1/10:ℝ))≤(b:ℝ) ∧
      (b:ℝ)≤Real.exp (2*(Fintype.card J:ℝ)*(Real.log x)^(1/5:ℝ)) := by
  let bands := fun j => markedLogPowerBand (e j) x
  change b∈Finset.univ.image (markedPrimeBandProduct bands) at hb
  obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hb
  have heq (a : ℝ) : (∏ _j : J,Real.exp a)=Real.exp ((Fintype.card J:ℝ)*a) := by
    rw [Finset.prod_const,Finset.card_univ,← Real.exp_nat_mul]
  have hlo (j : J) : Real.exp ((Real.log x)^(1/10:ℝ))≤(t j:ℝ) :=
    marked_band_common_lower (he j) hlog (t j).2
  have hhi (j : J) : (t j:ℝ)≤Real.exp (2*(Real.log x)^(1/5:ℝ)) :=
    (mem_markedLogPowerBand.mp (t j).2).2.2.trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hlog (heUpper j)) (by norm_num)))
  rw [markedPrimeBandProduct,Nat.cast_prod]
  constructor
  · rw [← heq]
    exact Finset.prod_le_prod₀ (fun _ _ => Real.exp_nonneg _) (fun j _ => hlo j)
  · calc
      _ ≤ ∏ _j : J,Real.exp (2*(Real.log x)^(1/5:ℝ)) :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun j _ => hhi j)
      _ = _ := (heq _).trans (congrArg Real.exp (by ring))

theorem markedTypeII_actual_label_dyads {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ)≤e j) (heUpper : ∀ j,e j≤(1/5:ℝ))
    (hgroups : 2≤Fintype.card J) :
    ∀ᶠ x : ℝ in atTop,
      let S := markedMajorLabelSet (fun j => markedLogPowerBand (e j) x)
      let I := markedTypeIILabelDyadIndices S
      ((I.card:ℝ)≤(1+2*(Fintype.card J:ℝ)/Real.log 2)*Real.log x) ∧
      (∀ j∈I,Real.exp ((Real.log x)^(1/10:ℝ))≤(2:ℝ)^j ∧
        (2:ℝ)^j≤Real.exp (2*(Fintype.card J:ℝ)*(Real.log x)^(1/5:ℝ))) ∧
      (∀ b∈S,(∑ j∈I,markedTypeIILabelCutoff ((b:ℝ)/(2:ℝ)^j))=1) := by
  have ht := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/10)).comp Real.tendsto_log_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop (Real.log 4)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hsmall hlog
  let S := markedMajorLabelSet (fun j => markedLogPowerBand (e j) x)
  let I := markedTypeIILabelDyadIndices S
  let L := Real.log x
  let E := Real.exp (L^(1/10:ℝ))
  let Z := Real.exp (2*(Fintype.card J:ℝ)*L^(1/5:ℝ))
  have hLp : 0<L := zero_lt_one.trans_le hlog
  have hZ : 1≤Z := Real.one_le_exp (by positivity)
  have hK : (2:ℝ)≤(Fintype.card J:ℝ) := by exact_mod_cast hgroups
  have hprod (b : ℕ) (hb : b∈S) := markedTypeII_actual_label_product_bounds e hlog he heUpper hb
  have hE₁ : 1≤E := Real.one_le_exp (Real.rpow_nonneg hLp.le _)
  have hE : 4*E ≤ Real.exp ((Fintype.card J:ℝ)*L^(1/10:ℝ)) := by
    calc
      _ = Real.exp (Real.log 4+L^(1/10:ℝ)) := by
        rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<4)]
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have hh := mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hLp.le (1/10:ℝ))
        change Real.log 4≤L^(1/10:ℝ) at hsmall
        linarith)
  have hI : (I.card:ℝ)≤(1+2*(Fintype.card J:ℝ)/Real.log 2)*L := by
    have hc := markedTypeIILabelDyad_card S Z hZ (fun b hb => (hprod b hb).2)
    have hp : L^(1/5:ℝ)≤L := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hlog
        (by norm_num : (1/5:ℝ)≤1)
    have hh := mul_le_mul_of_nonneg_left hp (show 0≤2*(Fintype.card J:ℝ)/Real.log 2 by positivity)
    apply hc.trans
    dsimp only [Z]
    rw [Real.log_exp]
    calc
      _ = 1+(2*(Fintype.card J:ℝ)/Real.log 2)*L^(1/5:ℝ) := by ring
      _ ≤ L+(2*(Fintype.card J:ℝ)/Real.log 2)*L := add_le_add hlog hh
      _ = _ := by ring
  refine ⟨hI,?_,?_⟩
  · intro j hj
    obtain ⟨b,hb,hη⟩ := (Finset.mem_filter.mp hj).2
    have hY : 0<(2:ℝ)^j := by positivity
    have hr := markedTypeIILabelCutoff_support hη
    have hb₁ : (2:ℝ)^j≤(b:ℝ) := by simpa only [one_mul] using (le_div_iff₀ hY).mp hr.1
    have hb₄ : (b:ℝ)≤4*(2:ℝ)^j := (div_le_iff₀ hY).mp hr.2
    exact ⟨by linarith [hE.trans ((hprod b hb).1.trans hb₄)],hb₁.trans (hprod b hb).2⟩
  · intro b hb
    have hb₂ : (2:ℝ)≤b := by linarith [hE.trans (hprod b hb).1]
    exact markedTypeIILabelDyad_partition S b hb (by exact_mod_cast hb₂)

end
end ArtinMatthews
