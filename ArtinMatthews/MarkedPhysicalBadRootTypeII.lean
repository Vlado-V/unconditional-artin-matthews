module

public import ArtinMatthews.MarkedPhysicalBadRootEnergy
public import ArtinMatthews.MarkedPhysicalEndpointNormActual
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

/-! Conditional bad-root energy for the original supported Type-II
coefficients, with beta's exact finite square sum retained. -/
namespace ArtinMatthews
noncomputable section
open Filter MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysicalRootBadVector_typeII_energy
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (hinj : Function.Injective e)
    (δ A : ℝ) (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop,∀ (d₀ Y : ℝ) (Z : Finset (ℤ × ℤ)) (U V : ℝ),
      Real.exp (L^(1/10:ℝ)) ≤ Y → 0 < U → 0 < V →
      (∀ z ∈ Z,U ≤ (z.1:ℝ) ∧ (z.1:ℝ) ≤ 16*U ∧ V ≤ (z.2:ℝ) ∧ (z.2:ℝ) ≤ 2*V) →
      ∀ (Sα Sβ : Finset ℕ) (modulation : ℝ) (β : ℕ → ℂ),
      (∀ n ∈ Sα,Real.exp (δ*L) ≤ (n:ℝ)) →
      (∫ θ : AddCircle (1:ℝ),
        ∑ s : MarkedPhysicalState (fun j => markedLogPowerBand (e j) (Real.exp L))
          (markedPadSlots (Real.exp L)) Z,
          markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) (Real.exp L)))
            (markedPadSlots (Real.exp L)) *
          ‖markedPhysicalRootBadVector e (Real.exp L) d₀ Y
            (markedMajorRestrictedCoefficient (Real.exp (L^(6/25:ℝ))) modulation Sα)
            (markedPhysicalRestrictedBeta Sβ β) θ s‖^2) ≤
        (16*U)*L^(4-A)*∑ s ∈ (Finset.Ioc 0 ⌊2*V⌋₊) ∩ Sβ,‖β s‖^2 := by
  filter_upwards [(Real.tendsto_exp_atTop.eventually (markedPhysicalRootBadVector_actual_energy e he hinj A)),
    markedPhysicalEndpointEnergy_actual_typeII e (fun j => by linarith [he j]) hinj δ hδ,
    eventually_gt_atTop (0:ℝ)] with L hb hephy hL
  intro d₀ Y Z U V hY hU hV hbox Sα Sβ modulation β hSα
  have hbad := hb d₀ Y Z
    (markedMajorRestrictedCoefficient (Real.exp (L^(6/25:ℝ))) modulation Sα)
    (markedPhysicalRestrictedBeta Sβ β) (by simpa only [Real.log_exp] using hY)
  simp only [Real.log_exp] at hbad
  have henergy := hephy (markedPadSlots (Real.exp L)) Z U V hU hV hbox Sα Sβ modulation β hSα
  apply hbad.trans
  calc
    _ ≤ L^(-A)*((16*U)*L^4*∑ s ∈ (Finset.Ioc 0 ⌊2*V⌋₊) ∩ Sβ,‖β s‖^2) :=
      mul_le_mul_of_nonneg_left henergy (Real.rpow_nonneg hL.le _)
    _ = _ := by rw [show L^(4-A)=L^(-A)*L^(4:ℝ) by rw [← Real.rpow_add hL]; congr 1; ring]; norm_num; ring

end
end ArtinMatthews
