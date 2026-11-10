module

public import ArtinMatthews.MarkedMajorArcCenteredCoefficient
public import ArtinMatthews.MarkedPhysicalCoprimeScalarDetector
public import ArtinMatthews.MarkedPhysicalPadSourceError
public import ArtinMatthews.MarkedPhysicalScalarCoefficients
public import ArtinMatthews.MarkedPhysicalTypeIIHarmonicSaving
public import ArtinMatthews.MarkedTypeIIScalarMajorJoin
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual scalar coprime minor estimate, with the two copied-pad
errors and the original physical detector saving on the same scale. -/
namespace ArtinMatthews
noncomputable section
open Filter

private theorem minor_absorb_three {D M D' M' : ℂ} {X L G : ℝ}
    (hX : 0 ≤ X) (hL : 3 ≤ L)
    (hD : ‖D-D'‖ ≤ X*L^(-(G+2))) (hM : ‖M-M'‖ ≤ X*L^(-(G+2)))
    (hP : ‖D'-M'‖ ≤ X*L^(-(G+2))) :
    ‖D-M‖ ≤ X*L^(-G) := by
  have hl : 0 < L := (by norm_num : (0:ℝ)<3).trans_le hL
  have hpow : L^(-(G+2))*L^2=L^(-G) := by
    rw [← Real.rpow_natCast L 2,← Real.rpow_add hl]
    congr 1
    push_cast
    ring
  have hl2 : (3:ℝ) ≤ L^2 := by nlinarith [mul_nonneg hl.le (sub_nonneg.mpr hL)]
  calc
    _ = ‖(D-D')+(D'-M')+(M'-M)‖ := by congr 1; ring
    _ ≤ ‖D-D'‖+‖D'-M'‖+‖M'-M‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ X*(3*L^(-(G+2))) := by rw [norm_sub_rev M' M]; linarith
    _ ≤ X*(L^2*L^(-(G+2))) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hl2 (Real.rpow_nonneg hl.le _)) hX
    _ = _ := by rw [mul_comm (L^2),hpow]

theorem markedPhysicalTypeIICoprimeCharacterMinor_actual_log_saving
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    (hinj : Function.Injective e) (Mχ : ℕ) (ξ : DirichletCharacter ℂ Mχ) {δ : ℝ} (hδ : 0 < δ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (R B W C G Kbox : ℝ) (hR : 0 ≤ R) (hB : 8 ≤ B) (hW : 0 ≤ W) (hC : 0 ≤ C)
    (hG : 0 ≤ G) (hKbox : 0 < Kbox)
    (hdepth : 100*(5*(G+2*C+11)+36)<(Fintype.card J:ℝ))
    (hηsupport : Function.support η ⊆ Set.Icc 1 4) (hη : ∀ t,‖η t‖ ≤ 1)
    (hψ : ∀ t,‖ψ t‖ ≤ W) (hψsupport : Function.support ψ ⊆ Set.Icc (-R) R) :
    ∀ᶠ x : ℝ in atTop,∀ (Y Hm Hn : ℝ),
      Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y → Y ≤ Real.exp (B*(Real.log x)^(1/5:ℝ)) →
      x^δ ≤ Hm → x^δ ≤ Hn → Hm*Hn ≤ Kbox*x →
      ∀ (S T : Finset ℕ) (modulation : ℝ) (β : ℕ → ℂ),
      (∀ m∈S,Hm ≤ (m:ℝ) ∧ (m:ℝ) ≤ 2*Hm) → (∀ n∈T,Hn ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*Hn) →
      (∀ n∈T,‖β n‖ ≤ (Real.log x)^C) →
      (∀ n∈T,β n ≠ 0 → ∀ p ∈ Nat.primesLE ⌊Real.exp ((Real.log x)^(6/25:ℝ))⌋₊,¬p∣n) →
      let bands := fun j => markedLogPowerBand (e j) x
      let Q := (Real.log x)^(G+2*C+20)
      let W₀ := Real.exp ((Real.log x)^(6/25:ℝ))
      ‖markedPhysicalCoprimeScalarDetectorSum bands S T η Y (markedBanEdgeKernel ψ Q Y)
        (fun n => ξ n*markedMajorCenteredCoefficient W₀ modulation n) (fun n => ξ n*β n)‖ ≤
        (Y*(Hm*Hn))*(Real.log x)^(-G) := by
  have hdepth' : 100*(5*((G+2)+2*C+9)+36)<(Fintype.card J:ℝ) := by linarith
  have hQexp : (G+2)+2*C+18=G+2*C+20 := by ring
  have hp := markedPhysicalTypeIICharacterHarmonicDifference_actual_log_saving e he heUpper hinj Mχ ξ
    hδ ψ η R B W C (G+2) hR hB hW hC (by positivity) hdepth' hηsupport hη hψ hψsupport
  have herr := markedPhysicalPadSource_errors_actual_log_saving e he heUpper hinj
    δ B R W Kbox C (G+2*C+20) (G+2) hδ hR hW hKbox (by positivity) η ψ hη hψ hηsupport hψsupport
  filter_upwards [hp,herr,eventually_gt_atTop (0:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (3:ℝ))] with x hphys herror hx hL
  intro Y Hm Hn hYlo hYhi hHm hHn hX S T modulation β hS hT hβnorm hβrough
  dsimp only
  have hY := (Real.exp_pos _).trans_le hYlo
  have hHm₀ := (Real.rpow_pos_of_pos hx δ).trans_le hHm
  have hHn₀ := (Real.rpow_pos_of_pos hx δ).trans_le hHn
  have hp' := hphys Y Hm Hn hYlo hYhi hHm hHn S T modulation β
    (fun m hm => hHm.trans (hS m hm).1) hβnorm
  dsimp only at hp'
  rw [hQexp] at hp'
  have hE := herror Y Hm Hn hY hYhi hHm hHn hX S T modulation β (fun n => ξ n)
    (fun n => ξ.norm_le_one n) hS hT hβnorm hβrough
  rw [← markedPhysicalCoprimeScalarDetectorSum_restricted_coefficients _ S T η Y
      (markedBanEdgeKernel ψ ((Real.log x)^(G+2*C+20)) Y) _ modulation β (fun n => ξ n),
    markedPhysicalCoprimeScalarDetectorSum_minor_split]
  exact minor_absorb_three (mul_nonneg hY.le (mul_nonneg hHm₀.le hHn₀.le)) hL hE.1 hE.2 hp'

end
end ArtinMatthews
