module

public import ArtinMatthews.MarkedPhysicalTypeIIDyadSum
public import ArtinMatthews.MarkedPhysicalPadDyadBudget
public import ArtinMatthews.MarkedPhysicalSourceErrorScale
public import ArtinMatthews.MarkedPhysicalTypeIIActual
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The original reciprocal dyad weight cancels the enlarged first box
side. The actual dyad count and a fixed log margin give the full sum. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Classical
noncomputable section

theorem markedPhysicalActualPadDyad_sum_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (heUpper : ∀ j,e j ≤ (1/5:ℝ)) (P : ℝ) :
    ∀ᶠ x : ℝ in atTop,∀ (X : ℝ),0 ≤ X → ∀ (f : ℕ → ℂ),
      (∀ j∈markedPhysicalPadDyadIndices (fun i => markedLogPowerBand (e i) x)
        ⌊(Real.log x)^(1/100:ℝ)⌋₊,‖f j‖ ≤ ((2:ℕ)^j:ℝ)*(X*(Real.log x)^(-(P+2)))) →
      ‖∑ j ∈ markedPhysicalPadDyadIndices (fun i => markedLogPowerBand (e i) x)
        ⌊(Real.log x)^(1/100:ℝ)⌋₊,(((2:ℕ)^j:ℝ):ℂ)⁻¹*f j‖ ≤ X*(Real.log x)^(-P) := by
  let D := 1+2*(Fintype.card J:ℝ)/Real.log 2
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 D))] with x hx
  intro X hX f hf
  let L := Real.log x
  have hL : 1 ≤ L := (le_max_left _ _).trans hx
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hD : D ≤ L := (le_max_right _ _).trans hx
  have hsmall : D*L^(-(P+1)) ≤ L^(-P) := by
    simpa only [Nat.cast_one,mul_one] using
      (markedPhysicalSourceErrorScale (N:=1) (G:=P) hL hD (by norm_num))
  have hpow : L*L^(-(P+2))=L^(-(P+1)) := by
    calc
      _ = L^(1:ℝ)*L^(-(P+2)) := by rw [Real.rpow_one]
      _ = L^((1:ℝ)+ -(P+2)) := (Real.rpow_add hLp _ _).symm
      _ = _ := by congr 1; ring
  apply (markedPhysicalPadDyad_weighted_norm_le _ _ f (X*L^(-(P+2))) hf).trans
  calc
    _ ≤ (D*L)*(X*L^(-(P+2))) := mul_le_mul_of_nonneg_right
      (markedPhysicalActualPadDyad_card e hL heUpper) (mul_nonneg hX (Real.rpow_nonneg hLp.le _))
    _ = X*(D*(L*L^(-(P+2)))) := by ring
    _ = X*(D*L^(-(P+1))) := by rw [hpow]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsmall hX

theorem markedPhysicalTypeIIDyadSum_actual_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    (hinj : Function.Injective e) {δ : ℝ} (hδ : 0 < δ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (K B W C P : ℝ) (hK : 0 ≤ K) (hB : 8 ≤ B) (hW : 0 ≤ W) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hdepth : 100*(5*(P+2*C+9)+36)<(Fintype.card J:ℝ))
    (hηsupport : Function.support η ⊆ Set.Icc 1 4) (hη : ∀ t,‖η t‖ ≤ 1)
    (hψ : ∀ t,‖ψ t‖ ≤ W) (hψsupport : Function.support ψ ⊆ Set.Icc (-K) K) :
    ∀ᶠ x : ℝ in atTop,∀ (Y Hm Hn : ℝ),
      Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y → Y ≤ Real.exp (B*(Real.log x)^(1/5:ℝ)) →
      x^δ ≤ Hm → x^δ ≤ Hn →
      ∀ (Sα Sβ : Finset ℕ) (modulation : ℝ) (β : ℕ → ℂ),
      (∀ n∈Sα,x^δ ≤ (n:ℝ)) → (∀ n∈Sβ,‖β n‖ ≤ (Real.log x)^C) →
      ‖markedPhysicalTypeIIDyadSum e x ψ η Y ((Real.log x)^(P+2*C+18)) Hm Hn
        Sα Sβ modulation β‖ ≤ (Y*(Hm*Hn))*(Real.log x)^(-P) := by
  have hB₀ : 0 ≤ B := by linarith
  have hE : 0 ≤ 2*(Fintype.card J:ℝ)+B := by positivity
  have hde : 100*(5*((P+2)+2*C+7)+36)=100*(5*(P+2*C+9)+36) := by ring
  have hdep : 100*(5*((P+2)+2*C+7)+36)<(Fintype.card J:ℝ) := hde.trans_lt hdepth
  have hQ : (P+2)+2*C+16=P+2*C+18 := by ring
  filter_upwards [markedPhysicalTypeIIPairing_actual_log_saving e he heUpper hinj hδ ψ η
      K (2*(Fintype.card J:ℝ)+B) B W C (P+2) hK hE hB hW hC (by linarith) hdep
      hηsupport hη hψ hψsupport,
    markedPhysicalActualPadDyad_sum_log_saving e heUpper P,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hphys hsum hx hlog
  intro Y Hm Hn hY hYhi hHm hHn Sα Sβ modulation β hSα hβ
  have hYp : 0 < Y := (Real.exp_pos _).trans_le hY
  have hY1 : 1 ≤ Y := (Real.one_le_exp (Real.rpow_nonneg (zero_le_one.trans hlog) _)).trans hY
  have hmp : 0 < Hm := (Real.rpow_pos_of_pos (zero_lt_one.trans hx) δ).trans_le hHm
  have hnp : 0 < Hn := (Real.rpow_pos_of_pos (zero_lt_one.trans hx) δ).trans_le hHn
  unfold markedPhysicalTypeIIDyadSum
  apply hsum (Y*(Hm*Hn)) (by positivity)
  intro j hj
  let d := ((2:ℕ)^j:ℝ)
  have hd : 1 ≤ d := (markedPhysicalActualPadDyad_scale e hlog heUpper j hj).1
  have hU : x^δ ≤ d*Y*Hm := hHm.trans
    (le_mul_of_one_le_left hmp.le (one_le_mul_of_one_le_of_one_le hd hY1))
  have hs := markedPhysicalActualPadDyad_Y_bound e hlog heUpper B Y hB₀ hYp.le hYhi j hj
  have hp := hphys d Y (zero_lt_one.trans_le hd) hY hYhi hs (d*Y*Hm) Hn hU hHn
    Sα Sβ modulation β hSα hβ
  rw [hQ] at hp
  exact hp.trans_eq (by ring)

theorem markedPhysicalTypeIICharacterDyadSum_actual_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    (hinj : Function.Injective e) (Mχ : ℕ) (ξ : DirichletCharacter ℂ Mχ) {δ : ℝ} (hδ : 0 < δ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (K B W C P : ℝ) (hK : 0 ≤ K) (hB : 8 ≤ B) (hW : 0 ≤ W) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hdepth : 100*(5*(P+2*C+9)+36)<(Fintype.card J:ℝ))
    (hηsupport : Function.support η ⊆ Set.Icc 1 4) (hη : ∀ t,‖η t‖ ≤ 1)
    (hψ : ∀ t,‖ψ t‖ ≤ W) (hψsupport : Function.support ψ ⊆ Set.Icc (-K) K) :
    ∀ᶠ x : ℝ in atTop,∀ (Y Hm Hn : ℝ),
      Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y → Y ≤ Real.exp (B*(Real.log x)^(1/5:ℝ)) →
      x^δ ≤ Hm → x^δ ≤ Hn →
      ∀ (Sα Sβ : Finset ℕ) (modulation : ℝ) (β : ℕ → ℂ),
      (∀ n∈Sα,x^δ ≤ (n:ℝ)) → (∀ n∈Sβ,‖β n‖ ≤ (Real.log x)^C) →
      ‖markedPhysicalTypeIICharacterDyadSum e x Mχ ξ ψ η Y ((Real.log x)^(P+2*C+18)) Hm Hn
        Sα Sβ modulation β‖ ≤ (Y*(Hm*Hn))*(Real.log x)^(-P) := by
  have hB₀ : 0 ≤ B := by linarith
  have hE : 0 ≤ 2*(Fintype.card J:ℝ)+B := by positivity
  have hde : 100*(5*((P+2)+2*C+7)+36)=100*(5*(P+2*C+9)+36) := by ring
  have hdep : 100*(5*((P+2)+2*C+7)+36)<(Fintype.card J:ℝ) := hde.trans_lt hdepth
  have hQ : (P+2)+2*C+16=P+2*C+18 := by ring
  filter_upwards [markedPhysicalTypeIICharacterPairing_actual_log_saving e he heUpper hinj Mχ ξ hδ ψ η
      K (2*(Fintype.card J:ℝ)+B) B W C (P+2) hK hE hB hW hC (by linarith) hdep
      hηsupport hη hψ hψsupport,
    markedPhysicalActualPadDyad_sum_log_saving e heUpper P,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hphys hsum hx hlog
  intro Y Hm Hn hY hYhi hHm hHn Sα Sβ modulation β hSα hβ
  have hYp : 0 < Y := (Real.exp_pos _).trans_le hY
  have hY1 : 1 ≤ Y := (Real.one_le_exp (Real.rpow_nonneg (zero_le_one.trans hlog) _)).trans hY
  have hmp : 0 < Hm := (Real.rpow_pos_of_pos (zero_lt_one.trans hx) δ).trans_le hHm
  have hnp : 0 < Hn := (Real.rpow_pos_of_pos (zero_lt_one.trans hx) δ).trans_le hHn
  unfold markedPhysicalTypeIICharacterDyadSum
  apply hsum (Y*(Hm*Hn)) (by positivity)
  intro j hj
  let d := ((2:ℕ)^j:ℝ)
  have hd : 1 ≤ d := (markedPhysicalActualPadDyad_scale e hlog heUpper j hj).1
  have hU : x^δ ≤ d*Y*Hm := hHm.trans
    (le_mul_of_one_le_left hmp.le (one_le_mul_of_one_le_of_one_le hd hY1))
  have hs := markedPhysicalActualPadDyad_Y_bound e hlog heUpper B Y hB₀ hYp.le hYhi j hj
  have hp := hphys d Y (zero_lt_one.trans_le hd) hY hYhi hs (d*Y*Hm) Hn hU hHn
    Sα Sβ modulation β hSα hβ
  rw [hQ] at hp
  exact hp.trans_eq (by ring)

end
end ArtinMatthews
