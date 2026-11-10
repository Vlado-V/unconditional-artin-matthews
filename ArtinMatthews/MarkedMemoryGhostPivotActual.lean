module

public import ArtinMatthews.MarkedMemoryGhostPivotMass
public import ArtinMatthews.MarkedMemoryBirthAtom
public import ArtinMatthews.MarkedMinorArcRawGhostActualRow
public import ArtinMatthews.MarkedMinorArcRawGhostConditional
public import ArtinMatthews.MarkedMinorArcRawGhostConditionalActual
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

/-! The actual conditional ghost row for a permutation event. Every
chronological nonpivot costs the proved tilted atom, with all birth
factorials, deletion eligibility and total memory caps still present. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedMemoryGhostPivot_actual_weighted_row_eventually
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) {q ρ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (hρ : 0 < ρ) (hgap : Real.sqrt q < ρ^2) :
    ∀ᶠ x : ℝ in atTop, ∀ (M B N : ℕ)
      (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) (t : Fin (N+1))
      (old : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes)
      (qStage : ℝ), 0 ≤ qStage → qStage ≤ Real.sqrt q →
      ∀ (m : MarkedRawMemory (markedRawActualPrimeBand e x) B)
        (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2),
      markedRawGhostConditionalWeightedAbsRow (markedRawActualPrimeAtom e q x)
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) qStage ρ
        (markedRawGhostSchurParameter q ρ) m z hz
        (fun _ l births => markedMemoryGhostPivotGate σ t old l.1 births) ≤
      (markedMemoryBirthAtomEnvelope x)^(markedMemoryStageNonpivots σ (2*t.1+1)).card*
        Real.exp ((Fintype.card J:ℝ)*(2*markedRawGhostSchurParameter q ρ/ρ)) := by
  filter_upwards [markedRawGhostConditional_actual_weighted_row_eventually e he hq₀ hq₁ hρ hgap,
    markedMemoryBirthAtom_actual_eventually e he,
    markedRawGhost_actual_band_mass_eventually e he] with x hrow hatom hmass
  intro M B N σ t old qStage hqs₀ hqs m z hz
  have hν : ∀ j p,0 ≤ markedRawActualPrimeAtom e q x j p := fun j p => (hatom q hq₀ hq₁ j p).1
  apply hrow qStage hqs₀ hqs B m z hz _
    (pow_nonneg (markedMemoryBirthAtomEnvelope_pos x).le _) _
  intro del l
  exact markedMemoryGhostPivot_factorial_mass_le (markedRawActualPrimeAtom e q x) hν
    (markedMemoryBirthAtomEnvelope_pos x).le (by norm_num : (1:ℝ) ≤ 2)
    (fun j p => (hatom q hq₀ hq₁ j p).2) (hmass q hq₀ hq₁) σ t old m del l

end ArtinMatthews
