module

public import ArtinMatthews.MarkedMinorArcRawPrimeBands
public import ArtinMatthews.MarkedEstimateMertensBands
public import ArtinMatthews.MarkedTypeIICollisionDecay
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

/-! A uniform single-atom envelope for the actual tilted birth laws. The
same literal ν is used at initial slots, fresh edge slots and ghost births. -/

noncomputable section
namespace ArtinMatthews
open Filter

def markedMemoryBirthAtomEnvelope (x : ℝ) : ℝ :=
  (4/Real.log 2)*Real.exp (-(Real.log x)^(1/10:ℝ))

theorem markedMemoryBirthAtomEnvelope_pos (x : ℝ) :
    0 < markedMemoryBirthAtomEnvelope x := by
  unfold markedMemoryBirthAtomEnvelope
  positivity

theorem markedMemoryBirthAtom_actual_eventually {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop, ∀ q : ℝ, 0 ≤ q → q ≤ 1 → ∀ j,
      ∀ p : ↥(markedRawActualPrimeBand e x j),
        0 ≤ markedRawActualPrimeAtom e q x j p ∧
          markedRawActualPrimeAtom e q x j p ≤ markedMemoryBirthAtomEnvelope x := by
  have hV := eventually_all.mpr (fun j => marked_log_power_band_mass_eventually
    (show 0 < e j by linarith [he j]))
  filter_upwards [marked_actual_tilted_atom_comparison_eventually e he,hV,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hν hV hlog
  intro q hq₀ hq₁ j p
  rw [markedRawActualPrimeAtom_eq_tilted]
  let p' := markedRawPrimeBandEquiv (markedLogPowerBand (e j) x)
    (fun _ hp => (mem_markedLogPowerBand.mp hp).1) p
  have hVp : 0 < bandReciprocalMass (markedLogPowerBand (e j) x) :=
    (by positivity : 0 < Real.log 2/2).trans (hV j).1
  have hp := markedHarmonicAtom_le (markedLogPowerBand (e j) x) hVp (Real.exp_pos _)
    (fun _ h => marked_band_common_lower (he j) hlog h) p'
  refine ⟨(hν q hq₀ hq₁ j p').1,?_⟩
  calc
    _ ≤ 2*markedHarmonicAtom (markedLogPowerBand (e j) x) p' := (hν q hq₀ hq₁ j p').2
    _ ≤ 2*((1/Real.exp ((Real.log x)^(1/10:ℝ)))/
        bandReciprocalMass (markedLogPowerBand (e j) x)) := by
      simpa only [div_div] using mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ) ≤ 2)
    _ ≤ 2*((1/Real.exp ((Real.log x)^(1/10:ℝ)))/(Real.log 2/2)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity)
        (by positivity : 0 < Real.log 2/2) (hV j).1.le) (by norm_num)
    _ = markedMemoryBirthAtomEnvelope x := by
      unfold markedMemoryBirthAtomEnvelope
      rw [Real.exp_neg]
      ring

end ArtinMatthews
