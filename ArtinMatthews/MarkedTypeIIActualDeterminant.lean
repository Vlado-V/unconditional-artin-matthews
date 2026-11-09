module

public import ArtinMatthews.MarkedPhysicalScalarMinorActual
public import ArtinMatthews.MarkedTypeIIDyadMajorError
public import ArtinMatthews.MarkedMajorFixedCharacterClosedIndex


set_option backward.privateInPublic true
@[expose] public section

/-! The actual occupied fixed-character determinant has logarithmic saving.
The scalar minor, original fixed-character major and shared-label error
use the same polynomial height. -/
namespace ArtinMatthews
open Filter Finset
open scoped ContDiff Classical
noncomputable section

theorem markedTypeII_determinant_triangle (det major minor : ℂ) {E : ℝ}
    (herr : ‖(det-major)-minor‖≤E) (hminor : ‖minor‖≤E) (hmajor : ‖major‖≤E) :
    ‖det‖≤3*E := by
  calc
    ‖det‖ = ‖(((det-major)-minor)+minor)+major‖ := by congr 1; ring
    _ ≤ ‖((det-major)-minor)+minor‖+‖major‖ := norm_add_le _ _
    _ ≤ (‖(det-major)-minor‖+‖minor‖)+‖major‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ _ := by linarith

theorem markedTypeII_actual_fixed_determinant_log_saving
    {J : Type} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (hinj : Function.Injective e)
    (he : ∀ j,(1/10:ℝ)<e j ∧ e j<(1/5:ℝ))
    {Mχ : ℕ} [NeZero Mχ] (ξ : DirichletCharacter ℂ Mχ)
    (δ C B Kbox D : ℝ) (hδ : 0<δ) (hC : 0≤C) (hB : 8≤B) (hKbox : 0<Kbox) (hD : 0≤D)
    (hdepth : 100*(5*(D+2*C+12)+36)<(Fintype.card J:ℝ)) :
    ∀ᶠ L : ℝ in atTop,∀ H U Y modulation : ℝ,∀ M N l r : ℕ,∀ β : ℕ → ℂ,
      Real.exp (δ*L)≤H → Real.exp (δ*L)≤U → H*U≤Kbox*Real.exp L →
      H≤(M:ℝ) → M≤N → (N:ℝ)≤2*H → U≤(l:ℝ) → (r:ℝ)≤2*U →
      Real.exp (L^(1/10:ℝ))≤Y → Y≤Real.exp (B*L^(1/5:ℝ)) →
      |modulation|≤L^C → (∀ n∈Icc l r,‖β n‖≤L^C) →
      (∀ n∈Icc l r,β n≠0 → ∀ p∈Nat.primesLE ⌊Real.exp (L^(6/25:ℝ))⌋₊,¬p∣n) →
      let P := fun j => markedLogPowerBand (e j) (Real.exp L)
      let W := Real.exp (L^(6/25:ℝ))
      let αχ := giantFixedCharacterReplacementCoefficient ξ W modulation
      let βχ := fun (n : ℕ) => ξ n*β n
      ‖markedTypeIIDeterminantSum (markedTypeIIOccupiedLabelEndpoints P Y (Icc M N) (Icc l r))
        (markedTypeIILabelEndpointCoefficient P Y αχ βχ)‖ ≤ (Y*(H*U))*L^(-D) := by
  have heLo : ∀ j,(1/10:ℝ)≤e j := fun j => (he j).1.le
  have heHi : ∀ j,e j≤(1/5:ℝ) := fun j => (he j).2.le
  have hcard : 0<(Fintype.card J:ℝ) := lt_trans (by positivity) hdepth
  let : Nonempty J := Fintype.card_pos_iff.mp (by exact_mod_cast hcard)
  let j₀ : J := Classical.choice inferInstance
  let A := D+1
  let Qexp := A+2*C+20
  have hA : 0≤A := by dsimp [A]; positivity
  have hQ : 0≤Qexp := by dsimp [Qexp]; positivity
  have hdepth' : 100*(5*(A+2*C+11)+36)<(Fintype.card J:ℝ) := by
    have heq : A+2*C+11=D+2*C+12 := by dsimp [A]; ring
    rwa [heq]
  have hmi := Real.tendsto_exp_atTop.eventually
    (markedPhysicalTypeIICoprimeCharacterMinor_actual_log_saving e heLo heHi hinj Mχ ξ hδ
      markedTypeIIDeterminantCutoff markedTypeIILabelCutoff 5 B 1 C A Kbox
      (by norm_num) hB (by norm_num) hC hA hKbox hdepth'
      markedTypeIILabelCutoff_support markedTypeIILabelCutoff_norm_le_one
      markedTypeIIDeterminantCutoff_norm_le_one markedTypeIIDeterminantCutoff_support)
  have hma := markedMajor_typeII_fixed_actual_Icc j₀ e hinj he ξ δ C Qexp Kbox A hδ hC hQ hA
    markedTypeIILabelCutoff markedTypeIILabelCutoff_contDiff markedTypeIILabelCutoff_norm_le_one
    (lo:=1) (hi:=4) (by norm_num) (by norm_num) (by norm_num) markedTypeIILabelCutoff_support
    markedTypeIIDeterminantCutoff markedTypeIIDeterminantCutoff_tsupport
  have heR := markedTypeII_actual_determinant_sub_major_error_log_saving e heLo ξ δ C Qexp Kbox A hδ hKbox
  filter_upwards [hmi,hma,heR,eventually_ge_atTop (3:ℝ)] with L hminor hmajor herr hL
  intro H U Y modulation M N l r β hH hU hX hHM hMN hNH hl hr hYlo hYhi hmod hβ hrough
  dsimp only
  let P := fun j => markedLogPowerBand (e j) (Real.exp L)
  let W := Real.exp (L^(6/25:ℝ))
  let αχ := giantFixedCharacterReplacementCoefficient ξ W modulation
  let βχ := fun (n : ℕ) => ξ n*β n
  let Det := markedTypeIIDeterminantSum (markedTypeIIOccupiedLabelEndpoints P Y (Icc M N) (Icc l r))
    (markedTypeIILabelEndpointCoefficient P Y αχ βχ)
  let Major := markedMajorFixedIntervalPairSum P ξ markedTypeIILabelCutoff markedTypeIIDeterminantCutoff
    (L^Qexp) Y W modulation (Icc M N) (Icc M N) l r β
  let Minor := markedPhysicalCoprimeScalarDetectorSum P (Icc M N) (Icc l r) markedTypeIILabelCutoff Y
    (markedBanEdgeKernel markedTypeIIDeterminantCutoff (L^Qexp) Y) αχ βχ
  have hY : 0<Y := (Real.exp_pos _).trans_le hYlo
  have hS (m : ℕ) (hm : m∈Icc M N) : H≤(m:ℝ) ∧ (m:ℝ)≤2*H :=
    ⟨hHM.trans (Nat.cast_le.mpr (mem_Icc.mp hm).1),(Nat.cast_le.mpr (mem_Icc.mp hm).2).trans hNH⟩
  have hT (n : ℕ) (hn : n∈Icc l r) : U≤(n:ℝ) ∧ (n:ℝ)≤2*U :=
    ⟨hl.trans (Nat.cast_le.mpr (mem_Icc.mp hn).1),(Nat.cast_le.mpr (mem_Icc.mp hn).2).trans hr⟩
  have hscale : (Real.exp L)^δ=Real.exp (δ*L) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos L),Real.log_exp,mul_comm L δ]
  have hMinor : ‖Minor‖≤(Y*(H*U))*L^(-A) := by
    have h := hminor Y H U (by simpa only [Real.log_exp] using hYlo)
      (by simpa only [Real.log_exp] using hYhi) (hscale.trans_le hH) (hscale.trans_le hU) hX
      (Icc M N) (Icc l r) modulation β hS hT
      (by simpa only [Real.log_exp] using hβ) (by simpa only [Real.log_exp] using hrough)
    have hα : αχ = (fun (n : ℕ) => ξ n*markedMajorCenteredCoefficient W modulation n) := rfl
    simpa only [Minor,hα,P,W,βχ,Qexp,Real.log_exp] using h
  have hMajor : ‖Major‖≤(Y*(H*U))*L^(-A) :=
    hmajor H U Y modulation M N l r β hH hU hX hHM hMN hNH hl hr hY hmod hβ hrough
  have hErr : ‖(Det-Major)-Minor‖≤(Y*(H*U))*L^(-A) :=
    herr H U Y modulation (Icc M N) l r β hH hU hX hS hl hr hY hβ
  have hroom : 3*L^(-A)≤L^(-D) := by
    simpa only [Nat.cast_one,mul_one,A] using
      (markedPhysicalSourceErrorScale (N:=1) (G:=D) (by linarith : 1≤L) hL (by norm_num))
  have hYX : 0≤Y*(H*U) := mul_nonneg hY.le
    (mul_nonneg ((Real.exp_pos _).le.trans hH) ((Real.exp_pos _).le.trans hU))
  change ‖Det‖ ≤ _
  calc
    _ ≤ 3*((Y*(H*U))*L^(-A)) := markedTypeII_determinant_triangle Det Major Minor hErr hMinor hMajor
    _ = (Y*(H*U))*(3*L^(-A)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hroom hYX

end
end ArtinMatthews
