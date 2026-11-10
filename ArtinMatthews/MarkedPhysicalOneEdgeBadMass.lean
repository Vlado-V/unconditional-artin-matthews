module

public import ArtinMatthews.MarkedPhysicalOneEdgeMass
public import ArtinMatthews.MarkedRawGoodRootMeasure
public import ArtinMatthews.MarkedEstimateMertensBands
public import ArtinMatthews.MarkedPhysicalEndpointNorm
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual independent-line, one-edge label/root exceptional mass.
The source list is the prefix of the union list, with every ordered label
and its single 1/(p+1) charge retained. -/
namespace ArtinMatthews
noncomputable section
open Filter MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedPhysicalUnionSource {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (a : MarkedPhysicalMarking P (M+1)) : MarkedPhysicalMarking P M :=
  fun j k => a j k.castSucc

theorem markedPhysical_one_edge_bad_label_root_mass
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (hinj : Function.Injective e) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop,∀ d₀ Y : ℝ,
      Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y →
      (∑ a : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) (markedPadSlots x+1),
        if MarkedPhysicalMarkingDistinct a then
          markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x+1) *
            markedPhysicalProjectiveProduct a *
            volume.real (markedRawBadRootSet e x d₀ Y
              ((markedPhysicalMarkingEquiv (fun j => markedLogPowerBand (e j) x)
                (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) (markedPadSlots x)).symm
                  (markedPhysicalUnionSource a))) else 0) ≤ (Real.log x)^(-A) := by
  have hepos : ∀ j,0 < e j := fun j => by linarith [he j]
  have hband := eventually_all.mpr (fun j => marked_log_power_band_mass_eventually (hepos j))
  filter_upwards [markedRawBadRootSet_log_saving e he hinj A,
    markedPhysical_actual_one_edge_label_mass e hepos,hband,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (0:ℝ))] with x hbad hmass hb hlog
  intro d₀ Y hY
  have hμ : 0 ≤ markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
      (markedPadSlots x+1) :=
    markedPhysicalMass_nonneg _ _ (fun j => ((by positivity : 0 < Real.log 2/2).trans (hb j).1).le)
  have hδ : 0 ≤ (Real.log x)^(-A) := Real.rpow_nonneg hlog _
  calc
    _ ≤ ∑ a : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) (markedPadSlots x+1),
        (Real.log x)^(-A) * (if MarkedPhysicalMarkingDistinct a then
          markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x+1) *
            markedPhysicalProjectiveProduct a else 0) := by
      apply Finset.sum_le_sum
      intro a _
      split_ifs
      · apply (mul_le_mul_of_nonneg_left (hbad d₀ Y hY _)
          (mul_nonneg hμ (by unfold markedPhysicalProjectiveProduct; positivity))).trans_eq
        ring
      · simp
    _ = (Real.log x)^(-A) *
        ∑ a : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) (markedPadSlots x+1),
          if MarkedPhysicalMarkingDistinct a then
            markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x+1) *
              markedPhysicalProjectiveProduct a else 0 := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_of_le_one_right hδ (hmass (markedPadSlots x))

end
end ArtinMatthews
