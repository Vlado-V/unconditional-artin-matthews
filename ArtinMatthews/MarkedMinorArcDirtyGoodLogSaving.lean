module

public import ArtinMatthews.MarkedMinorArcDirtyPromotedRow
public import ArtinMatthews.MarkedMinorArcDirtyScalar
public import ArtinMatthews.MarkedMinorArcDirtySecondGood
public import ArtinMatthews.MarkedMinorArcDirtyGoodDeltaRow
public import ArtinMatthews.MarkedMinorArcDirtyGoodEnvelope
public import ArtinMatthews.MarkedMinorArcDirtyMajorLogSaving
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

/-! The actual complete promoted-sector weighted row saves logarithmic
powers, with every store pattern and the genuine good cutoffs retained. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators

theorem markedDirty_good_promoted_row_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (hinj : Function.Injective e)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (v₀ c T A H W ρ L A₀ G : ℝ)
    (hv₀ : 1 ≤ v₀) (hc : 0 < c) (hT : 0 ≤ T) (hH : 0 ≤ H) (hW : 0 ≤ W)
    (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1) (hL : 0 ≤ L) (hdepth : 100*(G+2)<(Fintype.card J:ℝ))
    (hη : ∀ t,‖η t‖ ≤ H) (hψ : ∀ t,‖ψ t‖ ≤ W) (hsupp : Function.support ψ ⊆ Set.Icc (-A) A) :
    ∀ᶠ x : ℝ in atTop, ∀ (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
      (r d₀ Y q : ℝ) (w : Z → ℤ × ℤ)
      (χ : MarkedRawState (markedRawActualPrimeBand e x) (markedPadSlots x) (markedDirtyMemoryCutoff x) Z → ℂ)
      (s : MarkedRawState (markedRawActualPrimeBand e x) (markedPadSlots x) (markedDirtyMemoryCutoff x) Z)
      (modifier : (σ : J → Equiv.Perm (Fin (markedPadSlots x))) → MarkedRawEdgeChoice hZ (markedRawSlotEquiv σ s) → ℂ),
      Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y → 0 ≤ q → q ≤ 1 →
      (∀ z,markedMinorIntegerDet z.1 (w z)=1) →
      (∀ z ∈ Z,c ≤ |markedMinorIntegerTau r z| ∧ |markedMinorIntegerTau r z| ≤ T) →
      (∀ z v : Z,|markedMinorIntegerTau r v.1/markedMinorIntegerTau r z.1| ≤ 16) →
      (∀ s,‖χ s‖ ≤ 1) → (∀ σ c,‖modifier σ c‖ ≤ L) →
      markedDirtyPromotedWeightedRow (markedRawActualPrimeAtom e q x)
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) hZ ψ η r d₀ Y ((Real.log x)^A₀) ρ v₀ w
        (markedRawDirtySecondGoodCutoff e x r w χ) s modifier ≤ (Real.log x)^(-G) := by
  have hD : 0 ≤ markedDirtyPromotedDeltaConstant (Fintype.card J) ρ H W v₀ L := by
    unfold markedDirtyPromotedDeltaConstant
    exact mul_nonneg (mul_nonneg (by positivity) hL) (markedDirtyActualWeightedConstant_nonneg _ hv₀ hW)
  have hM : 0 ≤ markedDirtyPromotedMajorConstant (Fintype.card J) v₀ H W c T A L := by
    unfold markedDirtyPromotedMajorConstant
    exact mul_nonneg (mul_nonneg (by positivity) hL)
      (mul_nonneg (by norm_num) (markedDirtyMajorActualConstant_nonneg _ hv₀ hW))
  filter_upwards [markedDirty_good_promoted_row_envelope e he hinj ψ η v₀ c T A H W ρ L A₀
      hv₀ hc hT hH hW hρ₀ hρ₁ hL hη hψ hsupp,
    markedDirtyCombinedEnvelope_eventually_le hD hM (Fintype.card J) A₀ G hdepth] with x hx henv
  intro Z hZ r d₀ Y q w χ s modifier hY hq₀ hq₁ hw hτ hbox hχ hmodifier
  exact (hx Z hZ r d₀ Y q w χ s modifier hY hq₀ hq₁ hw hτ hbox hχ hmodifier).trans henv

end
end ArtinMatthews
