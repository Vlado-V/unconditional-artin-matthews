module

public import ArtinMatthews.MarkedMemoryDecoratedLifespans
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

/-! Reconstruction followed by canonical re-encoding preserves every
supplied lifespan label up to a constructed label equivalence. The finite
sum remains over the original slot and ordered-birth decorations. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

universe u w
variable {J : Type u} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)

theorem markedMemoryLifespanRunAddressEquiv_born {A : Type w}
    (d : MarkedMemoryLifespanRunData hZ s (n := n) A) (t : ℕ)
    (b : MarkedMemoryHistoryTraceBirth hZ (markedMemoryLifespanRunReconstruct hZ s d) t) :
    markedMemoryLifespanRunAddressEquiv hZ s d (Sum.inr ⟨t,b⟩) = d.born t b := rfl

/-- The reverse construction recovers the complete labeled interval data
up to an explicitly constructed identity renaming, not a bijection premise. -/
theorem markedMemoryLifespanRun_reencoding {A : Type w}
    (d : MarkedMemoryLifespanRunData hZ s (n := n) A) :
    ∃ e : MarkedMemoryHistoryTraceAddress hZ (markedMemoryLifespanRunReconstruct hZ s d) ≃ A,
      (∀ t i, e (markedMemoryLineageOrigin
        (T := MarkedMemoryHistoryTracePopulation hZ (markedMemoryLifespanRunReconstruct hZ s d))
        (Birth := MarkedMemoryHistoryTraceBirth hZ (markedMemoryLifespanRunReconstruct hZ s d))
        (markedMemoryHistoryTraceStep hZ (markedMemoryLifespanRunReconstruct hZ s d)) t i) = d.ids t i) ∧
      (∀ t b, e (Sum.inr ⟨t,b⟩) = d.born t b) ∧
      (∀ a, markedMemoryLineageBirthTime a = d.first (e a) ∧
        markedMemoryHistoryLifespanLast hZ (markedMemoryLifespanRunReconstruct hZ s d) a = d.last (e a) ∧
        d.prime (e a) = markedMemoryHistoryTraceAddressPrime hZ (markedMemoryLifespanRunReconstruct hZ s d) a ∧
        d.group (e a) = markedMemoryHistoryTraceAddressGroup hZ (markedMemoryLifespanRunReconstruct hZ s d) a) ∧
      markedMemoryRunHistoryEquiv hZ n s (markedMemoryLifespanRunReconstruct hZ s d) = d.events := by
  refine ⟨markedMemoryLifespanRunAddressEquiv hZ s d, ?_, ?_, ?_, ?_⟩
  · exact markedMemoryLifespanRunAddressEquiv_origin hZ s d
  · exact markedMemoryLifespanRunAddressEquiv_born hZ s d
  · intro a
    exact ⟨markedMemoryLifespanRunAddressEquiv_first hZ s d a,
      markedMemoryLifespanRunAddressEquiv_last hZ s d a,
      markedMemoryLifespanRunAddressEquiv_prime hZ s d a,
      markedMemoryLifespanRunAddressEquiv_group hZ s d a⟩
  · exact markedMemoryLifespanRunReconstruct_events hZ s d

variable [DecidableEq J]

/-- Exact finite coverage by canonical decorated lifespan realizations.
Arbitrary original summands retain their restrictions and multiplicities. -/
theorem markedMemoryCanonicalLifespan_sum {T : Type*} [AddCommMonoid T]
    (F : MarkedMemoryChronologicalHistory hZ n s → T) :
    (∑ events : MarkedMemoryRunHistory hZ n s,
      F (markedMemoryLifespanRunReconstruct hZ s (markedMemoryCanonicalLifespanRunData hZ s events))) =
      ∑ history : MarkedMemoryChronologicalHistory hZ n s, F history :=
  markedMemoryRunHistory_sum hZ n s F

/-- In particular the literal signed coefficient, every birth factorial,
both slot averages, and any original global restriction survive unchanged. -/
theorem markedMemoryCanonicalLifespan_weighted_sum
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (qStage : ℕ → ℝ) (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (j : ℕ)
    (keep : MarkedMemoryChronologicalHistory hZ n s → Prop)
    (f : MarkedRawState P (pads+1) B Z → ℂ) :
    (∑ events : MarkedMemoryRunHistory hZ n s,
      let history := markedMemoryLifespanRunReconstruct hZ s (markedMemoryCanonicalLifespanRunData hZ s events)
      if keep history then markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j history *
        f (markedMemoryChronologicalTarget hZ history) else 0) =
    ∑ history : MarkedMemoryChronologicalHistory hZ n s,
      if keep history then markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j history *
        f (markedMemoryChronologicalTarget hZ history) else 0 := by
  classical
  exact markedMemoryCanonicalLifespan_sum hZ s (fun history =>
    if keep history then markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j history *
      f (markedMemoryChronologicalTarget hZ history) else 0)

end
end ArtinMatthews
