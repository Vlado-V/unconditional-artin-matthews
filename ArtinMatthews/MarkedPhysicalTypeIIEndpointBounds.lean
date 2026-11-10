module

public import ArtinMatthews.MarkedPhysicalEndpointNormActual
public import ArtinMatthews.MarkedPhysicalCanonicalRoots
public import ArtinMatthews.FixedURootWeightedGeometry
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

/-! The original centered Type II alpha and supported beta give the
precise energy and supremum powers needed by localized moments. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Classical
noncomputable section

def markedPhysicalTypeIIEndpoint {J : Type*} [Fintype J]
    (e : J → ℝ) (x : ℝ) (Sα Sβ : Finset ℕ) (modulation : ℝ) (β : ℕ → ℂ)
    (z : ℤ × ℤ) : ℂ :=
  markedPhysicalEndpointVector (fun j => markedLogPowerBand (e j) x) (markedPadSlots x)
    (markedMajorRestrictedCoefficient (Real.exp ((Real.log x)^(6/25:ℝ))) modulation Sα)
    (markedPhysicalRestrictedBeta Sβ β) z

theorem markedPhysicalTypeIIEndpoint_bounds
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,0 < e j) (hinj : Function.Injective e)
    (δ C : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop,∀ (U V : ℝ),0 < U → 0 < V →
      ∀ (Sα Sβ : Finset ℕ) (modulation : ℝ) (β : ℕ → ℂ),
      (∀ n∈Sα,x^δ ≤ (n:ℝ)) → (∀ n∈Sβ,‖β n‖ ≤ (Real.log x)^C) →
      (∀ z : ℤ × ℤ,‖markedPhysicalTypeIIEndpoint e x Sα Sβ modulation β z‖^2 ≤
        (Real.log x)^(2*C+4)) ∧
      markedPhysicalEndpointEnergy (fun j => markedLogPowerBand (e j) x) (markedPadSlots x)
        (markedPhysicalPrimitiveBox U (16*U) V (2*V))
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
        (markedMajorRestrictedCoefficient (Real.exp ((Real.log x)^(6/25:ℝ))) modulation Sα)
        (markedPhysicalRestrictedBeta Sβ β) ≤ 32*(U*V)*(Real.log x)^(2*C+4) := by
  filter_upwards [markedPhysicalEndpointNorm_actual_typeII_log e he hinj δ hδ C,
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0:ℝ))] with x hx hlog
  intro U V hU hV Sα Sβ modulation β hSα hβ
  have hbox (z : ℤ × ℤ) (hz : z∈markedPhysicalPrimitiveBox U (16*U) V (2*V)) :
      U ≤ (z.1:ℝ) ∧ (z.1:ℝ) ≤ 16*U ∧ V ≤ (z.2:ℝ) ∧ (z.2:ℝ) ≤ 2*V := by
    have hb := Finset.mem_product.mp (Finset.mem_filter.mp hz).1
    have hu := (fixedURoot_mem_closed_interval U (16*U) z.1).mp hb.1
    have hv := (fixedURoot_mem_closed_interval V (2*V) z.2).mp hb.2
    exact ⟨hu.1,hu.2,hv.1,hv.2⟩
  have hb := hx (markedPadSlots x) (markedPhysicalPrimitiveBox U (16*U) V (2*V)) U V
    hU hV hbox Sα Sβ modulation β hSα hβ
  have hpow : ((Real.log x)^(C+2))^2=(Real.log x)^(2*C+4) := by
    rw [pow_two,← Real.rpow_add hlog]
    congr 1
    ring
  constructor
  · intro z
    exact (pow_le_pow_left₀ (norm_nonneg _) (hb.2 z) 2).trans_eq hpow
  · let E := markedPhysicalEndpointEnergy (fun j => markedLogPowerBand (e j) x) (markedPadSlots x)
      (markedPhysicalPrimitiveBox U (16*U) V (2*V))
      (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
      (markedMajorRestrictedCoefficient (Real.exp ((Real.log x)^(6/25:ℝ))) modulation Sα)
      (markedPhysicalRestrictedBeta Sβ β)
    have hE : 0 ≤ E := markedPhysicalEndpointEnergy_nonneg _ _ _ _
      (fun _ => by unfold bandReciprocalMass; positivity) _ _
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg E) hb.1 2
    change (Real.sqrt E)^2 ≤ (Real.sqrt (32*U*V)*(Real.log x)^(C+2))^2 at hsq
    rw [Real.sq_sqrt hE,mul_pow,Real.sq_sqrt (by positivity : (0:ℝ) ≤ 32*U*V),hpow] at hsq
    simpa only [mul_assoc] using hsq

end
end ArtinMatthews
