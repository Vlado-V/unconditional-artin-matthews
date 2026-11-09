module

public import ArtinMatthews.MarkedPhysicalPadCofactorHeight
public import ArtinMatthews.MarkedPhysicalPadScalarErrorActual


set_option backward.privateInPublic true
@[expose] public section

/-! Compare the original performed-box harmonic sum with the exact
scalar coprime detector under the original Type II cofactor hypotheses. -/
namespace ArtinMatthews
noncomputable section
open Filter

theorem markedPhysicalPadSource_errors_actual_log_saving
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    (hinj : Function.Injective e) (δ B R W K C Qexp G : ℝ)
    (hδ : 0 < δ) (hR : 0 ≤ R) (hW : 0 ≤ W) (hK : 0 < K) (hQexp : 0 ≤ Qexp)
    (η : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) (hη : ∀ u,‖η u‖ ≤ 1) (hψ : ∀ u,‖ψ u‖ ≤ W)
    (hηs : Function.support η ⊆ Set.Icc 1 4) (hψs : Function.support ψ ⊆ Set.Icc (-R) R) :
    ∀ᶠ x : ℝ in atTop,∀ (Y Hm Hn : ℝ),0 < Y → Y ≤ Real.exp (B*(Real.log x)^(1/5:ℝ)) →
      x^δ ≤ Hm → x^δ ≤ Hn → Hm*Hn ≤ K*x →
      ∀ (S T : Finset ℕ) (modulation : ℝ) (β ξ : ℕ → ℂ), (∀ n,‖ξ n‖ ≤ 1) →
      (∀ m∈S,Hm ≤ (m:ℝ) ∧ (m:ℝ) ≤ 2*Hm) → (∀ n∈T,Hn ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*Hn) →
      (∀ n∈T,‖β n‖ ≤ (Real.log x)^C) →
      (∀ n∈T,β n ≠ 0 → ∀ p ∈ Nat.primesLE ⌊Real.exp ((Real.log x)^(6/25:ℝ))⌋₊,¬p∣n) →
      let P := fun j => markedLogPowerBand (e j) x
      let M := ⌊(Real.log x)^(1/100:ℝ)⌋₊
      let Z := markedPhysicalTypeIIDyadBox Y Hm Hn
      let α' := fun n => ξ n*markedMajorRestrictedCoefficient (Real.exp ((Real.log x)^(6/25:ℝ))) modulation S n
      let β' := fun n => ξ n*markedPhysicalRestrictedBeta T β n
      let Δ := markedRawEdgeDeltaDetector ψ Y
      let H := markedRawEdgeMajorDetector ψ ((Real.log x)^Qexp) Y
      ‖markedPhysicalCoprimeScalarDetectorSum P S T η Y Δ α' β'-
        markedPhysicalHarmonicPaddedDetectorSum P M Z η Y Δ α' β'‖ ≤ (Y*(Hm*Hn))*(Real.log x)^(-G) ∧
      ‖markedPhysicalCoprimeScalarDetectorSum P S T η Y H α' β'-
        markedPhysicalHarmonicPaddedDetectorSum P M Z η Y H α' β'‖ ≤ (Y*(Hm*Hn))*(Real.log x)^(-G) := by
  filter_upwards [markedPhysicalPadScalarErrors_actual_log_saving e he heUpper hinj
    δ (4*K) 2 C Qexp R W (G+1) hδ (by positivity) hQexp hR hW η ψ hη hψ hηs hψs,
    markedPhysicalPadSource_harmonic_eq_survival e he heUpper hinj δ B R hδ hR η ψ hηs hψs,
    Real.tendsto_log_atTop.eventually (markedMajorTypeII_supported_alpha δ hδ),
    eventually_ge_atTop (1:ℝ),Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4:ℝ))]
    with x herr heq hα hx hL4
  intro Y Hm Hn hY hYhi hHm hHn hX S T modulation β ξ hξ hS hT hβnorm hβ
  dsimp only
  let L := Real.log x
  let W₀ := Real.exp (L^(6/25:ℝ))
  let Q := L^Qexp
  let Z := ⌊4*(Hm*Hn)⌋₊
  let α' := fun n => ξ n*markedMajorRestrictedCoefficient W₀ modulation S n
  let β' := fun n => ξ n*markedPhysicalRestrictedBeta T β n
  have hL : 0 < L := (by norm_num : (0:ℝ)<4).trans_le hL4
  have hs := markedPhysicalPadCofactor_height hx hδ.le hHm hHn hX S T hS hT
  have hscale : Real.exp (δ*Real.log x) = x^δ := by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans_le hx),mul_comm]
  have hα₁ := (hα S modulation (fun m hm => hscale.trans_le (hHm.trans (hS m hm).1))).1
  have hα' (m : ℕ) : ‖α' m‖ ≤ L^(2:ℝ) := by
    dsimp only [α']
    rw [norm_mul]
    simpa only [Real.rpow_two] using (mul_le_of_le_one_left (norm_nonneg _) (hξ m)).trans (hα₁ m)
  have hβ' (n : ℕ) : ‖β' n‖ ≤ L^C := by
    dsimp only [β']
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hξ n)).trans
      (markedPhysicalRestrictedBeta_bound T β (Real.rpow_nonneg hL.le _) hβnorm n)
  have hE := herr Y hY S T Z hs.1 hs.2.1 hs.2.2.2 α' β' (fun m _ => hα' m) (fun n _ => hβ' n)
  have hEq := heq Y Hm Hn Q hY hYhi hHm hHn S T modulation β ξ hS hT hβ
  have hP : L^(-(G+1))*L=L^(-G) := by
    calc
      _ = L^(-(G+1))*L^(1:ℝ) := by rw [Real.rpow_one]
      _ = L^(-(G+1)+1) := by rw [← Real.rpow_add hL]
      _ = _ := by congr 1; ring
  have hxδ := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hx) δ).le
  have hX₀ : 0 ≤ Y*(Hm*Hn) := mul_nonneg hY.le (mul_nonneg (hxδ.trans hHm) (hxδ.trans hHn))
  have hbound : Y*(Z:ℝ)*L^(-(G+1)) ≤ (Y*(Hm*Hn))*L^(-G) := by
    calc
      _ ≤ Y*(4*(Hm*Hn))*L^(-(G+1)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs.2.2.1 hY.le) (Real.rpow_nonneg hL.le _)
      _ = (Y*(Hm*Hn))*(L^(-(G+1))*4) := by ring
      _ ≤ (Y*(Hm*Hn))*(L^(-(G+1))*L) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL4 (Real.rpow_nonneg hL.le _))
          hX₀
      _ = _ := by rw [hP]
  constructor
  · rw [hEq.1]
    exact hE.1.trans hbound
  · rw [hEq.2]
    exact hE.2.trans hbound

end
end ArtinMatthews
