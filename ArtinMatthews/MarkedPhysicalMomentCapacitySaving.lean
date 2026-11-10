module

public import ArtinMatthews.MarkedMemoryOrphanTailDecay
public import ArtinMatthews.MarkedPhysicalCoordinateIndexCoefficient
public import ArtinMatthews.MarkedPhysicalMomentTube
public import ArtinMatthews.MarkedMemoryMomentOrphanSaving
public import ArtinMatthews.MarkedPhysicalCapacityCostAbsorption
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

/-! The full actual coordinate coefficient mass has the saving needed
before taking the original growing moment root. The finite source cutoff
and an arbitrary nonnegative constant prefactor are unchanged. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

theorem markedPhysicalCoordinateCapacity_actual_moment_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he0 : ∀ j,(1/10:ℝ) ≤ e j) (he1 : ∀ j,e j ≤ (1/5:ℝ))
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (K Hexp etaBound psiBound Qexp F G : ℝ) (hF : 0 ≤ F)
    (hK : 0 ≤ K) (hHexp : 0 ≤ Hexp) (heta : 0 ≤ etaBound) (hpsi : 0 ≤ psiBound)
    (hQexp : 0 ≤ Qexp) (hη : ∀ t,‖η t‖ ≤ etaBound) (hψ : ∀ t,‖ψ t‖ ≤ psiBound) :
    ∀ᶠ x : ℝ in atTop, ∀ (d₀ Y : ℝ),0 ≤ d₀ → 1 ≤ Y →
      d₀*Y ≤ Real.exp (Hexp*(Real.log x)^(21/100:ℝ)) →
      F * ((markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x) *
        (∑ i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
            (markedPadSlots x) (markedMemoryMomentLength x)
            (markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y)),
          ‖markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
            (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
            (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
            ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y ((Real.log x)^Qexp) i‖)) *
        markedMemoryOrphanTailEnvelope (80*(Fintype.card J:ℝ)) 1 x) ≤
          (Real.log x)^(-G*(markedMemoryMomentLength x:ℝ)) := by
  have hepos : ∀ j,0 < e j := fun j => by linarith [he0 j]
  filter_upwards [markedPhysicalCoordinateCoefficient_actual_total_budget e hepos he1 ψ η K Hexp
      etaBound psiBound Qexp hK hHexp heta hpsi hQexp hη hψ,
    markedMemoryOrphanTailEnvelope_moment_log_saving
      (markedPhysicalCoordinateCapacityCost (Fintype.card J) K Hexp etaBound psiBound Qexp) F G hF,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x ht he hlog
  intro d₀ Y hd₀ hY hscale
  have henv : 0 ≤ markedMemoryOrphanTailEnvelope (80*(Fintype.card J:ℝ)) 1 x := by
    unfold markedMemoryOrphanTailEnvelope
    positivity
  have hh := (mul_le_mul_of_nonneg_right (ht d₀ Y hd₀ hY hscale) henv).trans
    (markedPhysicalCoordinateCapacityCost_absorb (Fintype.card J) K Hexp etaBound psiBound Qexp hlog)
  exact (mul_le_mul_of_nonneg_left hh hF).trans he

end
end ArtinMatthews
