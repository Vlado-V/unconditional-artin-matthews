module

public import ArtinMatthews.MarkedPhysicalBonferroniTailMean
public import ArtinMatthews.MarkedPhysicalBonferroniHarmonic
public import ArtinMatthews.MarkedPhysicalBonferroniNumerical
public import ArtinMatthews.MarkedPhysicalPathBonferroni
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

/-! The actual performed residue-average odd tail saves every required
logarithmic power at the growing physical moment length, even after the
exp(O(log(x)^.73)) finite path budget. No independent-prime hypothesis is
assumed: the preceding CRT and one-prime estimates prove this bound. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators

theorem markedPhysicalActualBonferroniTailMean_log_saving
    {J : Type*} [Fintype J] (e : J → ℝ)
    (he : ∀ j,0 < e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    (hinj : Function.Injective e) (B A : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ x : ℝ in atTop,∀ (M : ℕ)
      (a : Fin (markedMemoryMomentLength x+1) →
        MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) M)
      (r : Fin (markedMemoryMomentLength x+1) → ℝ)
      (_hr : ∀ v,0 ≤ r v ∧ r v ≤ 1)
      (z : Fin (markedMemoryMomentLength x+1) → ℤ × ℤ)
      (hz : ∀ v,IsCoprime (z v).1 (z v).2),
      Real.exp (B*(Real.log x)^(73/100:ℝ))*
        markedPhysicalBonferroniTailMean (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
          Finset.univ a r z hz (2*markedPhysicalBonferroniDepth x+1) ≤
      (Real.log x)^(-A*(markedMemoryMomentLength x:ℝ)) := by
  filter_upwards [markedPhysicalActualBonferroniTailMean_bound e he heUpper hinj,
    markedPhysicalBonferroni_factorial_budget (Fintype.card J) B A (Nat.cast_nonneg _) hA]
    with x hmean hnum
  intro M a r hr z hz
  have hm := hmean M Finset.univ a r (fun v _ => hr v) z hz (2*markedPhysicalBonferroniDepth x+1)
  have hm' : markedPhysicalBonferroniTailMean (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
      Finset.univ a r z hz (2*markedPhysicalBonferroniDepth x+1) ≤
      markedFactorialTail ((Fintype.card J:ℝ)*((markedMemoryMomentLength x:ℝ)+1))
        (2*markedPhysicalBonferroniDepth x+1) := by
    simpa only [Finset.card_univ,Fintype.card_fin,Nat.cast_add,Nat.cast_one] using hm
  exact (mul_le_mul_of_nonneg_left hm' (Real.exp_nonneg _)).trans hnum

theorem markedPhysicalActualVisitQTailMean_log_saving
    {J : Type*} [Fintype J] (e : J → ℝ)
    (he : ∀ j,0 < e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    (hinj : Function.Injective e) (B A : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ x : ℝ in atTop,∀
      (a : Fin (markedMemoryMomentLength x+1) →
        MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) (markedPadSlots x))
      (q : ℝ) (_hq0 : 0 ≤ q) (_hq1 : q ≤ 1)
      (z : Fin (markedMemoryMomentLength x+1) → ℤ × ℤ)
      (hz : ∀ v,IsCoprime (z v).1 (z v).2),
      Real.exp (B*(Real.log x)^(73/100:ℝ))*
        markedPhysicalBonferroniTailMean (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
          Finset.univ a (markedMemoryVisitQ q (markedMemoryMomentLength x)) z hz
            (2*markedPhysicalBonferroniDepth x+1) ≤
      (Real.log x)^(-A*(markedMemoryMomentLength x:ℝ)) := by
  filter_upwards [markedPhysicalActualBonferroniTailMean_log_saving e he heUpper hinj B A hA]
    with x hx
  intro a q hq0 hq1 z hz
  exact hx (markedPadSlots x) a (markedMemoryVisitQ q (markedMemoryMomentLength x))
    (markedPhysicalVisitQ_mem_unitInterval hq0 hq1 _) z hz

end ArtinMatthews
