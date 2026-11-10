module

public import ArtinMatthews.MarkedPhysicalRootIncidenceError
public import ArtinMatthews.MarkedPhysicalActualLineMain
public import ArtinMatthews.MarkedPhysicalRootErrorBudget
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

/-! The actual union-label source, copied divisor and two new-slot products
in the incidence-preserving root error. No Haar or pairing bound is assumed. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedPhysicalActualIncidenceError {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ)
    (u : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) (markedPadSlots x+1))
    (hS : Squarefree (markedPhysicalMarkingProduct u))
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod (markedPhysicalMarkingProduct u)))
    (d₀ Y U V A B C D R Q : ℝ) (ψ : ℝ → ℂ) : ℝ :=
  markedPhysicalRootIncidenceDiscrepancy Finset.univ g U V A B C D
    (markedPhysicalBadArcLower e x (markedPhysicalActualEdgeRawSource e x u) d₀ Y)
    (markedPhysicalBadArcUpper e x (markedPhysicalActualEdgeRawSource e x u) d₀ Y)
    (markedPhysicalBadArcCoefficient e x (markedPhysicalActualEdgeRawSource e x u) d₀ Y)
    (markedPhysicalActualEdgeCopiedDivisor e x u)
    (markedPhysicalActualEdgeSourceProduct e x u)
    (markedPhysicalActualEdgeTargetProduct e x u) R Y Q
    (markedPhysicalEdgeRootLineEvent u hS g) ψ

theorem markedPhysicalActualIncidenceError_bound
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10 : ℝ) ≤ e j) (β H R : ℝ)
    (hβ : 0 ≤ β) (heβ : ∀ j,e j ≤ β) (hβhi : β+(1/100 : ℝ)<1)
    (hH : 0 ≤ H) (hR : 0 ≤ R) {δ : ℝ} (hδ : 0 < δ) (M : ℝ) :
    ∃ E : ℝ, 0 < E ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (u : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) (markedPadSlots x+1))
        (hS : Squarefree (markedPhysicalMarkingProduct u))
        (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod (markedPhysicalMarkingProduct u)))
        (d₀ Y U V A B C D Q W : ℝ) (ψ : ℝ → ℂ),
        x^δ ≤ U → x^δ ≤ V →
        (markedPhysicalMarkingProduct u : ℝ) ≤ Real.exp (M*(Real.log x)^(49/50 : ℝ)) →
        U ≤ A → A ≤ B → B ≤ 16*U → V ≤ C → C ≤ D → D ≤ 2*V →
        1 ≤ Q → Q ≤ Real.exp (H*(Real.log x)^(1/5 : ℝ)) →
        1 ≤ Y → Y ≤ Real.exp (H*(Real.log x)^(1/5 : ℝ)) →
        0 ≤ W → (∀ v,‖ψ v‖ ≤ W) →
        |markedPhysicalActualIncidenceError e x u hS g d₀ Y U V A B C D R Q ψ| ≤
          (5*E*W)*x^(-δ/2000) := by
  obtain ⟨E,hE,hcount⟩ := markedPhysicalRootIncidenceDiscrepancy_bound hδ M
  refine ⟨E,hE,?_⟩
  have hμ := eventually_all.mpr (fun I : Finset J =>
    marked_actual_harmonic_fresh_probability_eventually (fun j : ↥(Finset.univ \ I) => e j.1)
      (fun j => by linarith [he j.1]))
  filter_upwards [hcount,hμ,eventually_gt_atTop (0 : ℝ),
    markedPhysicalRoot_actual_error_budget e he β H R (δ/2000) hβ heβ hβhi hH hR
      (by positivity)] with x hx hμx hx0 hbudget
  intro u hS g d₀ Y U V A B C D Q W ψ hU hV hmod hUA hAB hB hVC hCD hD hQ hQhi hY hYhi hW hψ
  let source := markedPhysicalActualEdgeRawSource e x u
  have hm : (∑ i : MarkedPhysicalBadArcIndex e x source d₀ Y,
      |markedPhysicalBadArcCoefficient e x source d₀ Y i|) =
      markedRawBadRootArcComplexity e x d₀ Y source := by
    simp_rw [abs_of_nonneg (markedPhysicalBadArcCoefficient_nonneg e x source d₀ Y
      (fun I => (hμx I).1) _)]
    exact markedPhysicalBadArcCoefficient_sum e x source d₀ Y
  have hc := hx Finset.univ (markedPhysicalMarkingProduct u) g U V A B C D
    (markedPhysicalBadArcLower e x source d₀ Y)
    (markedPhysicalBadArcUpper e x source d₀ Y)
    (markedPhysicalBadArcCoefficient e x source d₀ Y)
    (markedPhysicalActualEdgeCopiedDivisor e x u)
    (markedPhysicalActualEdgeSourceProduct e x u)
    (markedPhysicalActualEdgeTargetProduct e x u) R Y Q W
    (markedPhysicalEdgeRootLineEvent u hS g) ψ
    hU hV hS hmod hUA hAB hB hVC hCD hD
    (fun i _ => markedPhysicalBadArc_bounds e x source d₀ Y i) hQ hY hW hψ
  rw [hm] at hc
  have hb : ((markedPhysicalRootTargetWindow (markedPhysicalActualEdgeCopiedDivisor e x u) R Y).card : ℝ)*
      markedRawBadRootArcComplexity e x d₀ Y source*Q^3 ≤ x^(δ/2000) := by
    change ((markedPhysicalRootTargetWindow
      (markedRawCopiedProduct ((markedRawActiveSplit ⌊(Real.log x)^(1/100 : ℝ)⌋₊) source).1 : ℤ) R Y).card : ℝ)*
        markedRawBadRootArcComplexity e x d₀ Y source*Q^3 ≤ x^(δ/2000)
    erw [markedRawCopiedProduct_eq_source]
    exact hbudget source (fun _ => Fin.last ⌊(Real.log x)^(1/100 : ℝ)⌋₊) d₀ Y Q
      hY hYhi (zero_le_one.trans hQ) hQhi
  calc
    _ ≤ (5*E*W)*x^(-δ/1000)*Q^3*
      ((markedPhysicalRootTargetWindow (markedPhysicalActualEdgeCopiedDivisor e x u) R Y).card : ℝ)*
        markedRawBadRootArcComplexity e x d₀ Y source := hc
    _ = ((5*E*W)*x^(-δ/1000))*
      (((markedPhysicalRootTargetWindow (markedPhysicalActualEdgeCopiedDivisor e x u) R Y).card : ℝ)*
        markedRawBadRootArcComplexity e x d₀ Y source*Q^3) := by ring
    _ ≤ ((5*E*W)*x^(-δ/1000))*x^(δ/2000) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by rw [mul_assoc,← Real.rpow_add hx0]; congr 2; ring

end ArtinMatthews
