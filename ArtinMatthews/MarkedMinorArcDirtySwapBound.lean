module

public import ArtinMatthews.MarkedMinorArcRawEdgeChargeSwap
public import ArtinMatthews.MarkedEstimateMertensBands
public import ArtinMatthews.MarkedMinorArcDirtyMajorActualTransfer
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

/-! The true original/reversed charge correction is uniformly bounded
on the actual logarithmic prime bands, independently of pending cutoff. -/
namespace ArtinMatthews
noncomputable section
open Filter

theorem markedRawEdgeChargeSwapModifier_actual_bound_eventually
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop, ∀ (q : ℝ),0 ≤ q → q ≤ 1 →
      ∀ (pads B : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
        (s : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z)
        (c : MarkedRawEdgeChoice hZ s),
        ‖markedRawEdgeChargeSwapModifier (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) hZ s c‖ ≤
          (2/Real.log 2)^(Fintype.card J) := by
  have hband := eventually_all.mpr (fun j => marked_log_power_band_mass_eventually
    (show 0 < e j by linarith [he j]))
  filter_upwards [hband,markedDirty_actual_band_transfer_eventually e he] with x hb ht
  intro q hq₀ hq₁ pads B Z hZ s c
  have h := ht q hq₀ hq₁
  exact markedRawEdgeChargeSwapModifier_norm_le _ (fun j => (h.2.1 j).1)
    markedDirty_transfer_constant_one_le
    (fun j => (hb j).2.le.trans markedDirty_transfer_constant_one_le)
    (fun j => (h.2.1 j).2) hZ s c

end
end ArtinMatthews
