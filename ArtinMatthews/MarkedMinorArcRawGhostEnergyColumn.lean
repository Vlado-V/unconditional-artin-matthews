module

public import ArtinMatthews.MarkedMinorArcRawGhostAbsoluteAction
public import ArtinMatthews.MarkedMinorArcRawGhostChoiceCauchy
public import ArtinMatthews.MarkedMinorArcRawGhostEnergyReduction
public import ArtinMatthews.MarkedMinorArcRawGhostEnergyTranspose
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! Exact evaluation of the full reverse Cauchy energy by the genuine
swapped weighted row. This is the missing column identity for the literal
factorial memory model, with repeated indexed particles retained. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

/-- Full source-mass integration of the actual reverse choice energy is
exactly target norm-square times the concrete swapped Schur row. -/
theorem markedRawGhostChoiceReverseEnergy_sum_eq_swapped_row
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    (V : J → ℝ) (hV : ∀ j, 0 ≤ V j) {qStage ρ v₀ : ℝ}
    (hq₀ : 0 ≤ qStage) (hq₁ : qStage ≤ 1) (hρ : 0 < ρ) (hv₀ : 0 < v₀)
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (f : MarkedRawState P M B Z → ℂ)
    (hf : ∀ z a, MarkedRawMemorySymmetric (fun m => f (z, (a, m)))) :
    (∑ s, markedRawStateMass ν s * markedRawGhostChoiceReverseEnergy ν V qStage ρ v₀ hZ f s) =
      ∑ s, markedRawStateMass ν s * ‖f s‖^2 *
        markedRawGhostSwappedWeightedAbsRow ν V qStage ρ v₀ s.2.2 s.1.1 (hZ _ s.1.2) := by
  classical
  apply Complex.ofReal_injective
  have ht := markedRawGhostAbsApply_transpose ν hν V hV hq₀ hq₁ hρ hZ
    (fun t => ((‖f t‖^2 / markedRawMemorySchurWeight v₀ t.2.2 : ℝ) : ℂ))
    (fun t => (markedRawMemorySchurWeight v₀ t.2.2 : ℂ))
    (markedRawGhostEnergyReweight_symmetric v₀ f hf)
    (fun _ _ => markedRawMemorySchurWeight_symmetric v₀)
  calc
    _ = ∑ s, (markedRawStateMass ν s : ℂ) * (markedRawMemorySchurWeight v₀ s.2.2 : ℂ) *
        markedRawGhostAbsApply ν V qStage ρ hZ
          (fun t => ((‖f t‖^2 / markedRawMemorySchurWeight v₀ t.2.2 : ℝ) : ℂ)) s := by
      simp only [Complex.ofReal_sum, Complex.ofReal_mul,
        markedRawGhostChoiceReverseEnergy_eq_absApply, mul_assoc]
    _ = _ := ht
    _ = _ := by
      simp only [Complex.ofReal_sum, Complex.ofReal_mul, mul_assoc]
      apply Finset.sum_congr rfl
      intro s _
      rw [markedRawGhostEnergyReweight_swapped_schur ν V qStage ρ hv₀ hZ f s]
      rw [Complex.ofReal_mul]

end
end ArtinMatthews
