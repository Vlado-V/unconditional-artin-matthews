module

public import ArtinMatthews.MarkedPhysicalMarking
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

/-! The one-edge independent-line label mass, charging each prime in
the union list exactly once by 1/(p+1). -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedPhysicalProjectiveProduct {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M : ℕ} (a : MarkedPhysicalMarking P M) : ℝ :=
  ∏ j,∏ k,1/((a j k:ℝ)+1)

theorem markedPhysicalProjectiveProduct_le_reciprocal
    {J : Type*} [Fintype J] {P : J → Finset ℕ}
    (hP : ∀ j p,p ∈ P j → p.Prime) {M : ℕ} (a : MarkedPhysicalMarking P M) :
    markedPhysicalProjectiveProduct a ≤ markedPhysicalReciprocalProduct a := by
  unfold markedPhysicalProjectiveProduct markedPhysicalReciprocalProduct
  apply Finset.prod_le_prod₀
  · intro j _
    exact Finset.prod_nonneg (fun k _ => by positivity)
  · intro j _
    apply Finset.prod_le_prod₀
    · intro k _
      positivity
    · intro k _
      exact one_div_le_one_div_of_le
        (by exact_mod_cast (hP j _ (a j k).2).pos) (by linarith)

theorem markedPhysical_one_edge_label_mass_le_one
    {J : Type*} [Fintype J] [DecidableEq J] (P : J → Finset ℕ)
    (hP : ∀ j p,p ∈ P j → p.Prime) (M : ℕ)
    (hV : ∀ j,0 < bandReciprocalMass (P j)) :
    (∑ a : MarkedPhysicalMarking P (M+1),if MarkedPhysicalMarkingDistinct a then
      markedPhysicalMass (fun j => bandReciprocalMass (P j)) (M+1) * markedPhysicalProjectiveProduct a
      else 0) ≤ 1 := by
  apply le_trans _ (markedPhysicalMarking_distinct_normalized_sum_le_one P (M+1) hV)
  apply Finset.sum_le_sum
  intro a _
  split_ifs
  · exact mul_le_mul_of_nonneg_left (markedPhysicalProjectiveProduct_le_reciprocal hP a)
      (markedPhysicalMass_nonneg _ _ (fun j => (hV j).le))
  · exact le_rfl

theorem markedPhysical_actual_one_edge_label_mass
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (he : ∀ j,0 < e j) :
    ∀ᶠ x : ℝ in atTop,∀ M : ℕ,
      (∑ a : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) (M+1),
        if MarkedPhysicalMarkingDistinct a then
          markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (M+1) *
            markedPhysicalProjectiveProduct a else 0) ≤ 1 := by
  filter_upwards [eventually_all.mpr (fun j => marked_log_power_band_mass_eventually (he j))] with x hx
  intro M
  exact markedPhysical_one_edge_label_mass_le_one _
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) M
    (fun j => (by positivity : 0 < Real.log 2/2).trans (hx j).1)

end
end ArtinMatthews
