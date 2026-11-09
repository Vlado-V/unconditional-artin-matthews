module

public import ArtinMatthews.MarkedPhysicalCharacterGoodSaving
public import ArtinMatthews.MarkedPhysicalCharacterGoodRemoval
public import ArtinMatthews.MarkedMinorArcRawLinePartition


set_option backward.privateInPublic true
@[expose] public section

/-! The literal fixed-character, unprojected physical Type II minor pairing follows
from a bound on its actual capped main term. Every endpoint, moment,
good-cutoff error and source logarithmic margin is derived. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Classical
noncomputable section

theorem markedPhysicalTypeIICharacterPairing_of_capped_bound
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    (hinj : Function.Injective e) (qχ : ℕ) (χ : DirichletCharacter ℂ qχ) {δ : ℝ} (hδ : 0 < δ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (K Hexp B etaBound psiBound Qexp C P : ℝ)
    (hK : 0 ≤ K) (hHexp : 0 ≤ Hexp) (hB : 8 ≤ B)
    (heta : 0 ≤ etaBound) (hpsi : 0 ≤ psiBound) (hQexp : 0 ≤ Qexp)
    (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hη : ∀ t,‖η t‖ ≤ etaBound) (hψ : ∀ t,‖ψ t‖ ≤ psiBound)
    (hψsupport : Function.support ψ ⊆ Set.Icc (-K) K) :
    ∀ᶠ x : ℝ in atTop,∀ (d₀ Y : ℝ) (hd₀ : 0 < d₀)
      (hY : Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y), Y ≤ Real.exp (B*(Real.log x)^(1/5:ℝ)) →
      d₀*Y ≤ Real.exp (Hexp*(Real.log x)^(21/100:ℝ)) →
      ∀ (q U V : ℝ),0 ≤ q → q ≤ 1 → x^δ ≤ U → x^δ ≤ V →
      let R := markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y)
      let hR := markedPhysicalMomentTubeRadius_ge_one (markedMemoryMomentLength x) hK
        (mul_nonneg hd₀.le ((Real.exp_pos _).le.trans hY))
      ‖markedPhysicalCoordinateCappedGlobal e x ψ η d₀ Y ((Real.log x)^Qexp) q U V R hR‖ ≤
        15*(Real.log x)^(-(P+2*C+7)*(markedMemoryMomentLength x:ℝ)) →
      ∀ (Sα Sβ : Finset ℕ) (modulation : ℝ) (β : ℕ → ℂ),
      (∀ n∈Sα,x^δ ≤ (n:ℝ)) → (∀ n∈Sβ,‖β n‖ ≤ (Real.log x)^C) →
      ‖markedPhysicalTypeIICharacterPairing e x qχ χ ψ η d₀ Y ((Real.log x)^Qexp) q U V
        Sα Sβ modulation β‖ ≤ (U*V)*(Real.log x)^(-P) := by
  filter_upwards [markedPhysicalTypeIICharacterGoodPairing_of_capped_bound e he heUpper hinj qχ χ hδ
    ψ η K Hexp B etaBound psiBound Qexp C (P+1) hK hHexp hB heta hpsi hQexp hC
      (by linarith) hη hψ hψsupport,
    markedPhysicalTypeIICharacterPairing_good_removal e he heUpper hinj qχ χ hδ ψ η K B etaBound psiBound
      Qexp C (P+1) hK hB heta hpsi hQexp hη hψ hψsupport,
    eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2:ℝ))]
    with x hgood hremove hx hlog
  intro d₀ Y hd₀ hY hYhi hscale q U V hq0 hq1 hU hV
  dsimp only
  intro hcap Sα Sβ modulation β hSα hβ
  let Z := markedPhysicalPrimitiveBox U (16*U) V (2*V)
  let w : Z → ℤ × ℤ := fun z => Classical.choose
    (markedPrimitivePosition_completion z.1 (Finset.mem_filter.mp z.2).2)
  have hw (z : Z) : markedMinorIntegerDet z.1 (w z)=1 := Classical.choose_spec
    (markedPrimitivePosition_completion z.1 (Finset.mem_filter.mp z.2).2)
  have hUp : 0 < U := (Real.rpow_pos_of_pos (zero_lt_one.trans hx) δ).trans_le hU
  have hVp : 0 < V := (Real.rpow_pos_of_pos (zero_lt_one.trans hx) δ).trans_le hV
  have huv : 0 < U*V := mul_pos hUp hVp
  have hshift : (P+1)+2*C+6=P+2*C+7 := by ring
  have hcap' : ‖markedPhysicalCoordinateCappedGlobal e x ψ η d₀ Y ((Real.log x)^Qexp)
      q U V (markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y))
      (markedPhysicalMomentTubeRadius_ge_one _ hK
        (mul_nonneg hd₀.le ((Real.exp_pos _).le.trans hY)))‖ ≤
      15*(Real.log x)^(-((P+1)+2*C+6)*(markedMemoryMomentLength x:ℝ)) := by
    rw [hshift]
    exact hcap
  have hg := hgood d₀ Y hd₀ hY hYhi hscale q U V hq0 hq1 hU hV hcap' w hw
    Sα Sβ modulation β hSα hβ
  have hr := (div_le_iff₀ huv).mp
    (hremove d₀ Y U V q hU hV hY hYhi w hw Sα Sβ modulation β hSα hβ)
  let f := markedPhysicalTypeIICharacterPairing e x qχ χ ψ η d₀ Y ((Real.log x)^Qexp) q U V Sα Sβ modulation β
  let g := markedPhysicalTypeIICharacterGoodPairing e x qχ χ ψ η d₀ Y ((Real.log x)^Qexp) q U V w
    Sα Sβ modulation β
  have hn : ‖f‖ ≤ ‖f-g‖+‖g‖ := by
    simpa only [sub_add_cancel] using norm_add_le (f-g) g
  have hsum : ‖f‖ ≤ (U*V)*(2*(Real.log x)^(-(P+1))) := by
    have hg' : ‖g‖ ≤ (U*V)*(Real.log x)^(-(P+1)) := hg
    have hr' : ‖f-g‖ ≤ (Real.log x)^(-(P+1))*(U*V) := hr
    linarith
  have hs : 2*(Real.log x)^(-(P+1)) ≤ (Real.log x)^(-P) := by
    simpa only [Nat.cast_one,mul_one] using
      (markedPhysicalSourceErrorScale (N:=1) (G:=P) (by linarith : 1 ≤ Real.log x) hlog (by norm_num))
  exact hsum.trans (mul_le_mul_of_nonneg_left hs huv.le)

end
end ArtinMatthews
