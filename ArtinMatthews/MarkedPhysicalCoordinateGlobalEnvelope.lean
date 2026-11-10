module

public import ArtinMatthews.MarkedPhysicalCoordinateCapacityGlobal
public import ArtinMatthews.MarkedPhysicalCoordinateCapacityEnvelope
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

/-! The globally summed actual correction has its literal scalar
majorant exposed, so stronger source asymptotics can be applied without
replacing the physical mass, carrier or coefficient norm sum. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Classical
noncomputable section

theorem markedPhysicalCoordinateCapacityGlobal_envelope
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (he : ∀ j,(1/10:ℝ)≤e j) :
    ∀ᶠ x : ℝ in atTop,∀ (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q U W : ℝ),
      0≤q → q≤1 → ∀ (B : ℕ) (hB : 1≤B),
      ‖markedPhysicalCoordinateCapacityGlobal e x ψ η d₀ Y Q q U W B hB‖≤
        15*(markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x)*
          (∑ i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
            (markedPadSlots x) (markedMemoryMomentLength x) B,
            ‖markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
              (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
              (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
              ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i‖))*
          markedMemoryOrphanTailEnvelope (80*(Fintype.card J:ℝ)) 1 x := by
  filter_upwards [markedPhysicalCoordinateCapacityTerm_envelope e he] with x ht
  intro ψ η d₀ Y Q q U W hq0 hq1 B hB
  let V := fun j => bandReciprocalMass (markedLogPowerBand (e j) x)
  have hv : ∀ j,0≤V j := by intro j; unfold V bandReciprocalMass; positivity
  have hm : 0 ≤ markedPhysicalMass V (markedPadSlots x) := markedPhysicalMass_nonneg V _ hv
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => ht V ψ η d₀ Y Q q U W hq0 hq1 B hB i)
  rw [← Finset.mul_sum] at hs
  unfold markedPhysicalCoordinateCapacityGlobal
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hm]
  apply ((mul_le_mul_of_nonneg_left (norm_sum_le _ _) hm).trans
    (mul_le_mul_of_nonneg_left hs hm)).trans_eq
  ring

end
end ArtinMatthews
