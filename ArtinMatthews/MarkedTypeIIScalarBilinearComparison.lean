module

public import ArtinMatthews.MarkedTypeIIScalarDeterminantComparison
public import ArtinMatthews.MarkedTypeIIQuotientDampedSaving


set_option backward.privateInPublic true
@[expose] public section

/-! Transfer of the literal full major form to the original marked rectangle.
All physical and shared-label errors, selected-square costs, and occupied dyad
summation are applied to the same arbitrary coefficient functions. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators
noncomputable section

theorem markedTypeII_scalar_rectangle_of_major
    {J : Type} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (hinj : Function.Injective e)
    (he : ∀ j,(1/10:ℝ) < e j ∧ e j < (1/5:ℝ))
    (δ Kbox Cα Cβ G : ℝ)
    (hδ : 0 < δ) (hKbox : 0 < Kbox) (hCα : 0 ≤ Cα) (hCβ : 0 ≤ Cβ) (hG : 0 ≤ G)
    (hdepth : 100*(5*(2*G+2*(Cα+Cβ)+16)+36)<(Fintype.card J:ℝ)) :
    ∀ᶠ x : ℝ in atTop, ∀ (Hm Hn : ℝ), x^δ ≤ Hm → x^δ ≤ Hn → Hm*Hn ≤ Kbox*x →
      ∀ (S T : Finset ℕ) (α β F : ℕ → ℂ),
      (∀ m ∈ S, Hm ≤ (m:ℝ) ∧ (m:ℝ) ≤ 2*Hm) →
      (∀ n ∈ T, Hn ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*Hn) →
      (∀ m ∈ S, ‖α m‖ ≤ (Real.log x)^Cα) →
      (∀ n ∈ T, ‖β n‖ ≤ (Real.log x)^Cβ) →
      let W := Real.exp ((Real.log x)^(6/25:ℝ))
      (∀ m ∈ S, α m ≠ 0 → MarkedPhysicalRoughAt W m) →
      (∀ n ∈ T, β n ≠ 0 → MarkedPhysicalRoughAt W n) →
      let P := fun j => markedLogPowerBand (e j) x
      let Q := (Real.log x)^(2*G+2*(Cα+Cβ)+25)
      (∀ h, ‖F h‖ ≤ 1) →
      (∀ j p, p ∈ P j → ∀ h, F (p*h) = F h) →
      (∀ j ∈ markedTypeIILabelDyadIndices (markedMajorLabelSet P), let Y := (2:ℝ)^j
        ‖markedTypeIIScalarFullMajor P S T markedTypeIILabelCutoff markedTypeIIDeterminantCutoff
            Q Y α β‖ ≤ Y*(Hm*Hn)*(Real.log x)^(-(2*G+8))) →
      ‖∑ m ∈ S, ∑ n ∈ T, α m*β n*F (m*n-1)*
        (literalMarkedArrayWeight e x (m*n-1):ℂ)‖ ≤ Hm*Hn*(Real.log x)^(-G) := by
  have hlo : ∀ j,(1/10:ℝ) ≤ e j := fun j => (he j).1.le
  have hhi : ∀ j,e j ≤ (1/5:ℝ) := fun j => (he j).2.le
  have hgroups : 2 ≤ Fintype.card J := by
    have h : (2:ℝ) ≤ (Fintype.card J:ℝ) :=
      (show (2:ℝ) ≤ 100*(5*(2*G+2*(Cα+Cβ)+16)+36) by linarith).trans hdepth.le
    exact_mod_cast h
  let : Nonempty J := Fintype.card_pos_iff.mp (by omega)
  let B := max 8 (2*(Fintype.card J:ℝ))
  let D := 2*G+8
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hdep : 100*(5*(D+2*(Cα+Cβ)+8)+36)<(Fintype.card J:ℝ) := by
    dsimp only [D]
    linarith
  have hQ : D+2*(Cα+Cβ)+17=2*G+2*(Cα+Cβ)+25 := by dsimp only [D]; ring
  have hsquare := Real.tendsto_log_atTop.eventually
    (giant_marked_quotient_damping_log_saving e hinj he δ Cα Cβ (G+1) hδ)
  filter_upwards [markedTypeII_actual_scalar_determinant_comparison e hlo hhi hinj δ B Cα Cβ D Kbox
      hδ (le_max_left _ _) hCα hCβ hD hKbox hdep,
    giantMarkedQuotientDampedSum_log_saving_of_determinants e hlo hhi hgroups δ Kbox Cα Cβ (G+1) hδ hKbox,
    markedTypeII_actual_label_dyads e hlo hhi hgroups, hsquare,
    eventually_ge_atTop (1:ℝ), Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2:ℝ))]
    with x hdet hdamped hlabels hsq hx hL₂
  intro Hm Hn hHm hHn hX S T α β F hS hT hα hβ
  dsimp only
  intro hrα hrβ hF hFinv hmajor
  let L := Real.log x
  let P := fun j => markedLogPowerBand (e j) x
  let Q := L^(2*G+2*(Cα+Cβ)+25)
  have hL : 1 ≤ L := (by norm_num : (1:ℝ) ≤ 2).trans hL₂
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hHm₀ : 0 < Hm := (Real.rpow_pos_of_pos hxp δ).trans_le hHm
  have hHn₀ : 0 < Hn := (Real.rpow_pos_of_pos hxp δ).trans_le hHn
  have hS' : ∀ m ∈ S, 0 < m ∧ (m:ℝ) ≤ 2*Hm := fun m hm =>
    ⟨Nat.cast_pos.mp (hHm₀.trans_le (hS m hm).1),(hS m hm).2⟩
  have hT' : ∀ n ∈ T, 0 < n ∧ (n:ℝ) ≤ 2*Hn := fun n hn =>
    ⟨Nat.cast_pos.mp (hHn₀.trans_le (hT n hn).1),(hT n hn).2⟩
  let K := giantMarkedQuotientDampedSum P S T α β F
  have hK : ‖K‖ ≤ Hm*Hn*L^(-(G+1)) := by
    apply hdamped Hm Hn hHm hHn hX S T hS' hT' α β F hα hβ hF
    intro j hj
    dsimp only
    let Y := (2:ℝ)^j
    obtain ⟨hylo,hyhi⟩ := hlabels.2.1 j hj
    have hy : Y ≤ Real.exp (B*L^(1/5:ℝ)) := hyhi.trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (zero_le_one.trans hL) _)))
    let Δ := markedTypeIIDeterminantSum (markedTypeIIOccupiedLabelEndpoints P Y S T)
      (markedTypeIILabelEndpointCoefficient P Y α β)
    let A := markedTypeIIScalarFullMajor P S T markedTypeIILabelCutoff markedTypeIIDeterminantCutoff Q Y α β
    have he : ‖Δ-A‖ ≤ Y*(Hm*Hn)*L^(-D) := by
      have hh := hdet Y Hm Hn hylo hy hHm hHn hX S T α β hS hT hα hβ hrα hrβ
      rw [hQ] at hh
      exact hh
    have ha : ‖A‖ ≤ Y*(Hm*Hn)*L^(-D) := hmajor j hj
    have hroom : 2*L^(-D) ≤ L^(-(2*(G+1)+5)) := by
      have hExp : 2*(G+1)+5+1=D := by dsimp only [D]; ring
      simpa only [Nat.cast_one,mul_one,hExp] using
        (markedPhysicalSourceErrorScale (N:=1) (G:=2*(G+1)+5) hL hL₂ (by norm_num))
    change ‖Δ‖ ≤ _
    calc
      _ ≤ ‖Δ-A‖+‖A‖ := by simpa only [sub_add_cancel] using norm_add_le (Δ-A) A
      _ ≤ Y*(Hm*Hn)*L^(-D)+Y*(Hm*Hn)*L^(-D) := add_le_add he ha
      _ = Y*(Hm*Hn)*(2*L^(-D)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hroom
        (mul_nonneg (pow_nonneg (by norm_num) _) (mul_pos hHm₀ hHn₀).le)
  have hscale : Real.exp (δ*Real.log x)=x^δ := by
    rw [Real.rpow_def_of_pos hxp,mul_comm]
  let U := ∑ m ∈ S, ∑ n ∈ T, α m*β n*F (m*n-1)*
    (literalMarkedArrayWeight e x (m*n-1):ℂ)
  have hUK : ‖U-K‖ ≤ Hm*Hn*L^(-(G+1)) := by
    simpa only [Real.exp_log hxp,hscale] using
      hsq Hm Hn S T α β F (hscale.trans_le hHm) (hscale.trans_le hHn) hS hT hα hβ hF
        (by simpa only [Real.exp_log hxp] using hFinv)
  have hroom : 2*L^(-(G+1)) ≤ L^(-G) := by
    simpa only [Nat.cast_one,mul_one] using
      (markedPhysicalSourceErrorScale (N:=1) (G:=G) hL hL₂ (by norm_num))
  change ‖U‖ ≤ _
  calc
    _ ≤ ‖U-K‖+‖K‖ := by simpa only [sub_add_cancel] using norm_add_le (U-K) K
    _ ≤ Hm*Hn*L^(-(G+1))+Hm*Hn*L^(-(G+1)) := add_le_add hUK hK
    _ = (Hm*Hn)*(2*L^(-(G+1))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hroom (mul_pos hHm₀ hHn₀).le

end
end ArtinMatthews
