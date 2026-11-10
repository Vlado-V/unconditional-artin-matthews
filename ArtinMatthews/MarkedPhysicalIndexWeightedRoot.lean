module

public import ArtinMatthews.MarkedPhysicalIndexRootGeometry
public import ArtinMatthews.MarkedRootConstantIndicator
public import ArtinMatthews.MarkedPhysicalCoordinateUniform
public import ArtinMatthews.MarkedRootWeightedPathBudget
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Actual weighted root replacement on the pure coordinate index.
The coefficient bound and bounded completions are proved for every
index; no physical state or nonzero lift is selected. -/

noncomputable section
namespace ArtinMatthews
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

theorem markedPhysicalMomentLength_exp_99 {x B : ℝ}
    (hlog : 1≤Real.log x) (hB : 8≤B) :
    (markedMemoryMomentLength x:ℝ)+1≤Real.exp (B*(Real.log x)^(99/100:ℝ)) := by
  have hs := Real.one_le_rpow hlog (by norm_num : (0:ℝ)≤1/2)
  have hc := Nat.ceil_lt_add_one (div_nonneg (Real.rpow_nonneg (zero_le_one.trans hlog) (1/2:ℝ))
    (by norm_num : (0:ℝ)≤2))
  have hn : (markedMemoryMomentLength x:ℝ)+1≤4*(Real.log x)^(1/2:ℝ) := by
    unfold markedMemoryMomentLength
    push_cast
    linarith
  have hp : (Real.log x)^(1/2:ℝ)≤(Real.log x)^(99/100:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)
  have he := Real.add_one_le_exp (B*(Real.log x)^(99/100:ℝ))
  have hz := Real.rpow_nonneg (zero_le_one.trans hlog) (99/100:ℝ)
  nlinarith

theorem markedPhysicalCoordinateIndex_weighted_root_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ)≤e j) (heUpper : ∀ j,e j≤(1/5:ℝ))
    {δ : ℝ} (hδ : 0<δ) (Mr B C G A : ℝ) (hB : 8≤B) (hG : 0≤G) (hA : 0≤A)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (Hη W v₀ : ℝ)
    (hHη : 0≤Hη) (hW : 0≤W) (hv0 : 0<v₀)
    (hη : ∀ t,‖η t‖≤Hη) (hψ : ∀ t,‖ψ t‖≤W) :
    ∀ᶠ x : ℝ in atTop,∀ (V : J → ℝ) (R : ℕ)
      (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
        (markedPadSlots x) (markedMemoryMomentLength x) R) (hR : 1≤R)
      (S : ℕ) (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) (U Vr d₀ Y Q r : ℝ),
      (∀ j,v₀≤V j) → x^δ≤U → x^δ≤Vr → Squarefree S →
      (S:ℝ)≤Real.exp (Mr*(Real.log x)^(49/50:ℝ)) →
      Real.exp ((Real.log x)^(1/10:ℝ))≤Y → Y≤Real.exp (B*(Real.log x)^(1/5:ℝ)) →
      (R:ℝ)+1≤Real.exp (B*(Real.log x)^(99/100:ℝ)) →
      1≤Q → Q≤(Real.log x)^A → 0≤r → r≤1 →
      let κ := (r:ℂ)*markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
        (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i
      Real.exp (C*(Real.log x)^(99/100:ℝ))*
        (‖markedRootConstantIndicatorSum g U Vr (markedPhysicalCoordinateIndexGoodSet e x d₀ Y U Vr i hR) κ-
          (U*Vr/((riemannZeta 2).re*(Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)):ℝ))) •
            (markedPhysicalCoordinateIndexGoodVolume e x d₀ Y U Vr i hR • κ)‖/(U*Vr)) ≤
        (Real.log x)^(-G*(markedMemoryMomentLength x:ℝ)) := by
  let C₀ := markedPhysicalCoordinateUniformBound (Fintype.card J) v₀ Hη W
  have hC₀ : 0≤C₀ := markedPhysicalCoordinateUniformBound_nonneg _ hv0 hW
  have hroot := markedRootGoodPath_weighted_log_budget e he (49/50) (by norm_num)
    (fun j => (heUpper j).trans (by norm_num)) (by norm_num) hδ Mr B C G A C₀
    (by linarith) hG hA hC₀
  simp only [show max ((49/50:ℝ)+1/100) (1/5)=99/100 by norm_num] at hroot
  filter_upwards [hroot,Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx hlog
  intro V R i hR S g U Vr d₀ Y Q r hV hU hVr hS hSr hY hYhi hRhi hQ hQhi hr0 hr1
  let κ := (r:ℂ)*markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i
  have hY1 : 1≤Y := (Real.one_le_exp (Real.rpow_nonneg (zero_le_one.trans hlog) _)).trans hY
  have hc := markedPhysicalCoordinateIndexCoefficient_norm_le (fun j => markedLogPowerBand (e j) x)
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q
    Hη W hY1 hQ hHη hW hη hψ i
  have hcoeff : ‖markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i‖ ≤
      (C₀*Q^3)^(markedMemoryMomentLength x) := by
    apply hc.trans
    exact pow_le_pow_left₀ (by unfold markedPhysicalCoordinateEdgeBound; positivity)
      (mul_le_mul_of_nonneg_right (markedPhysicalCoordinateEdgeBound_le V hv0 hV hW) (by positivity)) _
  have hκ : ‖κ‖≤(C₀*Q^3)^(markedMemoryMomentLength x) := by
    have hr : ‖(r:ℂ)‖≤1 := by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr0] using hr1
    dsimp only [κ]
    rw [norm_mul]
    exact (mul_le_mul hr hcoeff (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  let z := fun v => markedPhysicalCoordinateIndexPath i.2.1 v
  let w := fun v => markedPrimitiveCoordinateCompletion (z v) (markedPhysicalCoordinateIndexPath_primitive hR i.2.1 v)
  have hz (v) (k : Fin 2) : |markedRootIntegerVector (z v) k|≤(R:ℝ)+1 := by
    have hh := markedPhysicalCoordinateIndexPath_real_bound hR i.2.1 v
    fin_cases k
    · change |((z v).1:ℝ)|≤(R:ℝ)+1
      exact hh.1.trans (by linarith)
    · change |((z v).2:ℝ)|≤(R:ℝ)+1
      exact hh.2.trans (by linarith)
  have hw (v) (k : Fin 2) : |markedRootIntegerVector (w v) k|≤(R:ℝ)+1 := by
    have hh := markedPhysicalCoordinateIndexCompletion_bound hR i.2.1 v
    fin_cases k
    · change |((w v).1:ℝ)|≤(R:ℝ)+1
      exact hh.1
    · change |((w v).2:ℝ)|≤(R:ℝ)+1
      exact hh.2
  have hd (v) : markedVectorDet (markedRootIntegerVector (z v)) (markedRootIntegerVector (w v))=1 := by
    have hh : (markedMinorIntegerDet (z v) (w v):ℝ)=1 := by
      exact_mod_cast markedPrimitiveCoordinateCompletion_det (z v) (markedPhysicalCoordinateIndexPath_primitive hR i.2.1 v)
    simpa only [markedMinorIntegerDet,Int.cast_sub,Int.cast_mul,markedVectorDet,markedRootIntegerVector,
      Matrix.cons_val_zero,Matrix.cons_val_one] using hh
  have ho := hx Finset.univ (markedPhysicalCoordinateIndexRawActive (fun j => markedLogPowerBand (e j) x)
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) ⌊(Real.log x)^(1/100:ℝ)⌋₊ i)
    S g U Vr d₀ Y ((R:ℝ)+1) (fun v => markedRootIntegerVector (z v))
    (fun v => markedRootIntegerVector (w v)) Q κ hU hVr hS hSr hY hYhi (by positivity) hRhi
    (by simpa only [Finset.card_univ,Fintype.card_fin,Nat.cast_add,Nat.cast_one] using
      markedPhysicalMomentLength_exp_99 hlog hB)
    (fun v _ => hd v) (fun v _ => hz v) (fun v _ => hw v) hQ hQhi hκ
  change Real.exp (C*(Real.log x)^(99/100:ℝ))*
    (‖markedRootConstantIndicatorSum g U Vr (markedPhysicalCoordinateIndexGoodSet e x d₀ Y U Vr i hR) κ-
      (U*Vr/((riemannZeta 2).re*(Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)):ℝ))) •
        (∫ p,(if p∈markedPhysicalCoordinateIndexGoodSet e x d₀ Y U Vr i hR then κ else 0)
          ∂markedNormalizedRootMeasure)‖/(U*Vr))≤_ at ho
  rw [markedRootConstantIndicator_integral _
    (markedPhysicalCoordinateIndexGoodSet_measurable e x d₀ Y U Vr i hR),
    markedPhysicalCoordinateIndexGoodSet_volume] at ho
  exact ho

end ArtinMatthews
