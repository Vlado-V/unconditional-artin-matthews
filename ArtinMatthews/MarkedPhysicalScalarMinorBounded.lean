module

public import ArtinMatthews.MarkedPhysicalScalarHarmonicActual
public import ArtinMatthews.MarkedPhysicalPadSourceError
public import ArtinMatthews.MarkedPhysicalScalarCoefficients
public import ArtinMatthews.MarkedTypeIIScalarMajorJoin


set_option backward.privateInPublic true
@[expose] public section

/-! The actual coprime scalar minor estimate for arbitrary bounded rough
coefficients. The support, primitive boxes and copied-pad collisions are restored exactly. -/
namespace ArtinMatthews
open Filter
open scoped Classical
noncomputable section

private theorem markedPhysicalRestrictedScalar_support (S : Finset ℕ) (α : ℕ → ℂ) (W : ℝ)
    (hα : ∀ m∈S,α m ≠ 0 → MarkedPhysicalRoughAt W m) :
    ∀ m, markedPhysicalRestrictedBeta S α m ≠ 0 → m ∈ S ∧ MarkedPhysicalRoughAt W m := by
  intro m hm
  have h : m∈S ∧ α m ≠ 0 := by
    simpa only [markedPhysicalRestrictedBeta, ite_ne_right_iff] using hm
  exact ⟨h.1,hα m h.1 h.2⟩

/-- The actual scalar determinant kernel with its major part removed,
for any bounded rough coefficient rectangle. -/
theorem markedPhysicalTypeIICoprimeMinor_bounded_log_saving
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    (hinj : Function.Injective e) {δ : ℝ} (hδ : 0 < δ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (R B W Cα Cβ G Kbox : ℝ) (hR : 0 ≤ R) (hB : 8 ≤ B) (hW : 0 ≤ W)
    (hCα : 0 ≤ Cα) (hCβ : 0 ≤ Cβ) (hG : 0 ≤ G) (hKbox : 0 < Kbox)
    (hdepth : 100*(5*(G+2*(Cα+Cβ)+7)+36)<(Fintype.card J:ℝ))
    (hηsupport : Function.support η ⊆ Set.Icc 1 4) (hη : ∀ t,‖η t‖ ≤ 1)
    (hψ : ∀ t,‖ψ t‖ ≤ W) (hψsupport : Function.support ψ ⊆ Set.Icc (-R) R) :
    ∀ᶠ x : ℝ in atTop,∀ (Y Hm Hn : ℝ),
      Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y → Y ≤ Real.exp (B*(Real.log x)^(1/5:ℝ)) →
      x^δ ≤ Hm → x^δ ≤ Hn → Hm*Hn ≤ Kbox*x →
      ∀ (S T : Finset ℕ) (α β : ℕ → ℂ),
      (∀ m∈S,Hm ≤ (m:ℝ) ∧ (m:ℝ) ≤ 2*Hm) → (∀ n∈T,Hn ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*Hn) →
      (∀ m∈S,‖α m‖ ≤ (Real.log x)^Cα) → (∀ n∈T,‖β n‖ ≤ (Real.log x)^Cβ) →
      let W₀ := Real.exp ((Real.log x)^(6/25:ℝ))
      (∀ m∈S,α m ≠ 0 → MarkedPhysicalRoughAt W₀ m) →
      (∀ n∈T,β n ≠ 0 → MarkedPhysicalRoughAt W₀ n) →
      let bands := fun j => markedLogPowerBand (e j) x
      let Q := (Real.log x)^(G+2*(Cα+Cβ)+16)
      ‖markedPhysicalCoprimeScalarDetectorSum bands S T η Y (markedBanEdgeKernel ψ Q Y) α β‖ ≤
        (Y*(Hm*Hn))*(Real.log x)^(-G) := by
  let Qexp := G+2*(Cα+Cβ)+16
  have hQ : (G+2)+2*(Cα+Cβ)+14=Qexp := by dsimp only [Qexp]; ring
  have hdep : 100*(5*((G+2)+2*(Cα+Cβ)+5)+36)<(Fintype.card J:ℝ) := by linarith
  have hbands := eventually_all.mpr (fun j => marked_log_power_band_mass_eventually
    ((by norm_num : (0:ℝ)<1/10).trans_le (he j)))
  filter_upwards [markedPhysicalScalarHarmonic_actual_log_saving e he heUpper hinj hδ ψ η
      R B W Cα Cβ (G+2) hR hB hW hCα hCβ (by positivity) hdep hηsupport hη hψ hψsupport,
    markedPhysicalPadScalarErrors_actual_log_saving e he heUpper hinj δ (4*Kbox) Cα Cβ Qexp
      R W (G+3) hδ (by positivity) (by dsimp only [Qexp]; positivity) hR hW
      η ψ hη hψ hηsupport hψsupport,
    markedPhysicalPadSource_cutoffs e heUpper B R hR, hbands, marked_array_disjoint_eventually e hinj,
    eventually_ge_atTop (1:ℝ),Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4:ℝ))]
    with x hphys herr hcut hmass hdis hx hL4
  intro Y Hm Hn hYlo hYhi hHm hHn hX S T α β hS hT hα hβ
  dsimp only
  intro hαrough hβrough
  let L := Real.log x
  let Q := L^Qexp
  let P := fun j => markedLogPowerBand (e j) x
  let pads := ⌊L^(1/100:ℝ)⌋₊
  let W₀ := Real.exp (L^(6/25:ℝ))
  let α' := markedPhysicalRestrictedBeta S α
  let β' := markedPhysicalRestrictedBeta T β
  let Δ := markedRawEdgeDeltaDetector ψ Y
  let H := markedRawEdgeMajorDetector ψ Q Y
  let X := Y*(Hm*Hn)
  have hY := (Real.exp_pos _).trans_le hYlo
  have hxδ := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hx) δ).le
  have hX₀ : 0 ≤ X := mul_nonneg hY.le (mul_nonneg (hxδ.trans hHm) (hxδ.trans hHn))
  have hL : 1 ≤ L := (by norm_num : (1:ℝ)≤4).trans hL4
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hV (j : J) : 0 < bandReciprocalMass (P j) :=
    (show 0 < Real.log 2/2 by positivity).trans (hmass j).1
  have hP (j : J) (p : ℕ) (hp : p∈P j) : p.Prime := (mem_markedLogPowerBand.mp hp).1
  have hα' := markedPhysicalRestrictedBeta_bound S α (Real.rpow_nonneg hLpos.le _) hα
  have hβ' := markedPhysicalRestrictedBeta_bound T β (Real.rpow_nonneg hLpos.le _) hβ
  have hrα := markedPhysicalRestrictedScalar_support S α W₀ hαrough
  have hrβ := markedPhysicalRestrictedScalar_support T β W₀ hβrough
  have hbelow := (hcut Y hY hYhi).1
  have hsupp := markedPhysical_delta_major_small_support ψ hY hψsupport (hcut Y hY hYhi).2 Q
  let Z := markedPhysicalTypeIIDyadBox Y Hm Hn
  have heΔ : markedPhysicalHarmonicPaddedDetectorSum P pads Z η Y Δ α' β' =
      markedPhysicalPadSurvivalScalarSum P pads S T η Y Δ α' β' :=
    markedPhysicalHarmonicPaddedDetectorSum_eq_survival_scalar P hP hdis hV pads
      hY (hxδ.trans hHm) (hxδ.trans hHn) hbelow hηsupport hsupp.1 S T hS hT hrα hrβ
  have heH : markedPhysicalHarmonicPaddedDetectorSum P pads Z η Y H α' β' =
      markedPhysicalPadSurvivalScalarSum P pads S T η Y H α' β' :=
    markedPhysicalHarmonicPaddedDetectorSum_eq_survival_scalar P hP hdis hV pads
      hY (hxδ.trans hHm) (hxδ.trans hHn) hbelow hηsupport hsupp.2 S T hS hT hrα hrβ
  have hh : ‖markedPhysicalHarmonicPaddedDetectorSum P pads Z η Y Δ α' β'-
      markedPhysicalHarmonicPaddedDetectorSum P pads Z η Y H α' β'‖ ≤ X*L^(-(G+2)) := by
    have h := hphys Y Hm Hn hYlo hYhi hHm hHn α' β' hα' hβ'
    dsimp only at h
    rw [hQ] at h
    exact h
  rw [heΔ,heH] at hh
  have hs := markedPhysicalPadCofactor_height hx hδ.le hHm hHn hX S T hS hT
  let B₀ := ⌊4*(Hm*Hn)⌋₊
  have hE := herr Y hY S T B₀ hs.1 hs.2.1 hs.2.2.2 α' β' (fun m _ => hα' m) (fun n _ => hβ' n)
  have hbound : Y*(B₀:ℝ)*L^(-(G+3)) ≤ X*L^(-(G+2)) := by
    have hpow : 4*L^(-(G+3)) ≤ L^(-(G+2)) := by
      simpa only [Nat.cast_one,mul_one,show G+2+1=G+3 by ring] using
        (markedPhysicalSourceErrorScale (N:=1) (G:=G+2) hL hL4 (by norm_num))
    calc
      _ ≤ Y*(4*(Hm*Hn))*L^(-(G+3)) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hs.2.2.1 hY.le) (Real.rpow_nonneg hLpos.le _)
      _ = X*(4*L^(-(G+3))) := by dsimp only [X]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow hX₀
  have hnormΔ := hE.1.trans hbound
  have hnormH := hE.2.trans hbound
  rw [← markedPhysicalCoprimeScalarDetectorSum_congr_coefficients P S T η Y (markedBanEdgeKernel ψ Q Y)
      (α := α') (β := β') (α' := α) (β' := β)
      (fun m hm => ite_eq_left hm) (fun n hn => ite_eq_left hn),
    markedPhysicalCoprimeScalarDetectorSum_minor_split]
  let D₀ := markedPhysicalCoprimeScalarDetectorSum P S T η Y Δ α' β'
  let M₀ := markedPhysicalCoprimeScalarDetectorSum P S T η Y H α' β'
  let D' := markedPhysicalPadSurvivalScalarSum P pads S T η Y Δ α' β'
  let M' := markedPhysicalPadSurvivalScalarSum P pads S T η Y H α' β'
  change ‖D₀-M₀‖ ≤ X*L^(-G)
  have htriangle : ‖D₀-M₀‖ ≤ ‖D₀-D'‖+‖D'-M'‖+‖M₀-M'‖ := by
    calc
      _ = ‖(D₀-D')+(D'-M')+(M'-M₀)‖ := by congr 1; ring
      _ ≤ ‖D₀-D'‖+‖D'-M'‖+‖M'-M₀‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = _ := by rw [norm_sub_rev M' M₀]
  have hsmall : 3*L^(-(G+2)) ≤ L^(-G) := by
    apply le_trans ?_ (Real.rpow_le_rpow_of_exponent_le hL (by linarith : -(G+1)≤ -G))
    simpa only [Nat.cast_one,mul_one,show G+1+1=G+2 by ring] using
      (markedPhysicalSourceErrorScale (N:=1) (G:=G+1) hL ((by norm_num : (3:ℝ)≤4).trans hL4) (by norm_num))
  apply htriangle.trans
  calc
    _ ≤ X*(3*L^(-(G+2))) := by
      change ‖D₀-D'‖ ≤ X*L^(-(G+2)) at hnormΔ
      change ‖M₀-M'‖ ≤ X*L^(-(G+2)) at hnormH
      change ‖D'-M'‖ ≤ X*L^(-(G+2)) at hh
      linarith
    _ ≤ _ := mul_le_mul_of_nonneg_left hsmall hX₀

end
end ArtinMatthews
