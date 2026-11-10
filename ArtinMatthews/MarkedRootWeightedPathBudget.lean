module

public import ArtinMatthews.MarkedRootConstantIndicator
public import ArtinMatthews.MarkedPhysicalCoordinateLogBudget
public import ArtinMatthews.MarkedRootGoodPathBudget
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! The actual full-good root comparison tolerates a logarithmic cost
per edge. This finite scalar helper is specialized below to the proved
literal physical coordinate-copy norm, not a smoothness assumption. -/

noncomputable section
namespace ArtinMatthews
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

theorem markedRootGoodPath_weighted_log_budget {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (β : ℝ) (hβ : 0 ≤ β)
    (heβ : ∀ j,e j ≤ β) (hβhi : β+(1/100:ℝ)<1)
    {δ : ℝ} (hδ : 0 < δ) (Mr B C G A C₀ : ℝ)
    (hB : 0 ≤ B) (hG : 0 ≤ G) (hA : 0 ≤ A) (hC₀ : 0 ≤ C₀) :
    let α := max (β+1/100) (1/5:ℝ)
    ∀ᶠ x : ℝ in atTop,∀ {ι : Type*} (I : Finset ι)
      (source : ι → MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
      (S : ℕ) (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) (U V d₀ Y H : ℝ)
      (z w : ι → Fin 2 → ℝ) (Q : ℝ) (κ : ℂ),
      x^δ ≤ U → x^δ ≤ V → Squarefree S →
      (S:ℝ) ≤ Real.exp (Mr*(Real.log x)^(49/50:ℝ)) →
      Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y → Y ≤ Real.exp (B*(Real.log x)^(1/5:ℝ)) →
      0 ≤ H → H ≤ Real.exp (B*(Real.log x)^α) →
      (I.card:ℝ) ≤ Real.exp (B*(Real.log x)^α) →
      (∀ k ∈ I,markedVectorDet (z k) (w k)=1) →
      (∀ k ∈ I,∀ j,|z k j| ≤ H) → (∀ k ∈ I,∀ j,|w k j| ≤ H) →
      1 ≤ Q → Q ≤ (Real.log x)^A →
      ‖κ‖ ≤ (C₀*Q^3)^(markedMemoryMomentLength x) →
      Real.exp (C*(Real.log x)^α)*
        (‖markedRootConstantIndicatorSum g₀ U V (markedRootGoodPathSet e x I source d₀ Y U V z w) κ-
          (U*V/((riemannZeta 2).re*(Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)):ℝ))) •
            (∫ p,(if p ∈ markedRootGoodPathSet e x I source d₀ Y U V z w then κ else 0) ∂markedNormalizedRootMeasure)‖/(U*V)) ≤
        (Real.log x)^(-G*(markedMemoryMomentLength x:ℝ)) := by
  dsimp only
  have hG' : 0 ≤ G+3*A+1 := by linarith
  filter_upwards [markedRootGoodPath_replacement_log_budget e he β hβ heβ hβhi hδ Mr B C
      (G+3*A+1) hB hG',markedPhysicalCoordinate_log_absorption C₀ A G hC₀,
    eventually_gt_atTop (1:ℝ)] with x hx hnum hx1
  intro ι I source S g₀ U V d₀ Y H z w Q κ hU hV hS hSr hY hYhi hH hHhi hI hdet hz hw hQ hQhi hκ
  have hUp : 0 < U := (Real.rpow_pos_of_pos (zero_lt_one.trans hx1) δ).trans_le hU
  have hVp : 0 < V := (Real.rpow_pos_of_pos (zero_lt_one.trans hx1) δ).trans_le hV
  let E := Real.exp (C*(Real.log x)^(max (β+1/100) (1/5:ℝ)))*
    (|(markedRootIndicatorCount g₀ U V (markedRootGoodPathSet e x I source d₀ Y U V z w):ℝ)-
      (U*V/((riemannZeta 2).re*(Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)):ℝ)))*
        markedNormalizedRootMeasure.real (markedRootGoodPathSet e x I source d₀ Y U V z w)|/(U*V))
  have hE : 0 ≤ E := mul_nonneg (Real.exp_pos _).le (div_nonneg (abs_nonneg _) (mul_pos hUp hVp).le)
  have hEhi : E ≤ (Real.log x)^(-(G+3*A+1)*(markedMemoryMomentLength x:ℝ)) :=
    hx I source S g₀ U V d₀ Y H z w hU hV hS hSr hY hYhi hH hHhi hI hdet hz hw
  have hfinal := hnum Q E (markedMemoryMomentLength x) hQ hQhi hE hEhi
  rw [markedRootGoodPath_constant_error e x I source d₀ Y U V z w g₀ κ]
  have heq : Real.exp (C*(Real.log x)^(max (β+1/100) (1/5:ℝ)))*
      (‖κ‖*|(markedRootIndicatorCount g₀ U V (markedRootGoodPathSet e x I source d₀ Y U V z w):ℝ)-
        (U*V/((riemannZeta 2).re*(Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)):ℝ)))*
          markedNormalizedRootMeasure.real (markedRootGoodPathSet e x I source d₀ Y U V z w)|/(U*V)) = ‖κ‖*E := by
    dsimp only [E]
    ring
  rw [heq]
  exact (mul_le_mul_of_nonneg_right hκ hE).trans hfinal

end ArtinMatthews
