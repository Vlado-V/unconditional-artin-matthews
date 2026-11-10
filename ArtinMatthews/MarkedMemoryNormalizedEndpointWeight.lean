module

public import ArtinMatthews.MarkedMemoryNormalizedHistoryIndex
public import ArtinMatthews.MarkedMemoryIndependentBirthFactorials
public import ArtinMatthews.MarkedMemoryIndependentBirthWeight
public import ArtinMatthews.MarkedMemoryIndependentRunCount
public import ArtinMatthews.MarkedMemoryIndependentSourceScalar
public import ArtinMatthews.MarkedMemoryIndependentWeight
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

/-! Elementwise source weights on normalized finite endpoint data. The
direct scalar uses the real first/last and active incidences; the exact
birth factorial and full signed edge residual remain separate factors. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)

def markedMemoryIndependentEndpointScalar
    (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
    (q : ℝ) (a : Σ j,A j) : ℝ :=
  ∏ v : Fin (n+1),
    (if (d.lifespan a.1).first a.2≤2*v.val ∧ 2*v.val≤(d.lifespan a.1).last a.2 ∧
        ¬(d.lifespan a.1).active (2*v.val) a.2 then
      (if (d.lifespan a.1).last a.2=2*v.val then
        -markedMemoryEta q n v*markedMemoryIndependentLineHit hZ d a v
       else 1-markedMemoryEta q n v*markedMemoryIndependentLineHit hZ d a v)
     else 1) *
    (if (d.lifespan a.1).first a.2=2*v.val+1 ∧ 2*v.val+1≤(d.lifespan a.1).last a.2 ∧
        ¬(d.lifespan a.1).active (2*v.val) a.2 then
      -markedMemoryEta q n v*markedMemoryIndependentLineHit hZ d a v else 1)

theorem markedMemoryIndependentEndpointScalar_eq
    (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
    (q : ℝ) (a : Σ j,A j) :
    markedMemoryIndependentEndpointScalar hZ d q a=markedMemoryIndependentLifespanSourceScalar hZ d q a :=
  (markedMemoryIndependentLifespanSourceScalar_endpoints hZ d q a).symm

variable (s : MarkedRawState P (pads+1) B Z)
  (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
  (d₀ Y Q : ℝ) (q : ℝ) (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)

def markedMemoryNormalizedEndpointWeight
    (i : MarkedMemoryNormalizedHistoryIndex (A := A) (n := n) hZ s) : ℂ :=
  let d := markedMemoryFiniteTableau_toIndependent hZ i.1.1.1
  let H := markedMemoryIndependentHistory hZ d i.1.2
  (((∏ a : Σ j,A j,markedMemoryIndependentBirthMass hZ d ν V a *
      (V a.1)⁻¹ ^ markedMemoryIndependentRunCount hZ d a *
      markedMemoryIndependentEndpointScalar hZ d q a) /
      markedMemoryIndependentBirthFactorials hZ d : ℝ) : ℂ) *
    markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n 0 H

theorem markedMemoryNormalizedEndpointWeight_eq
    (i : MarkedMemoryNormalizedHistoryIndex (A := A) (n := n) hZ s) :
    markedMemoryNormalizedEndpointWeight hZ s ν V ψ η d₀ Y Q q χ i=
      markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q 1
        (markedMemoryHistoryVisitSchedule q n) χ n 0 (markedMemoryNormalizedHistoryAssembly hZ s i) := by
  rcases i with ⟨⟨⟨f,hs⟩,order⟩,hn⟩
  cases hs
  simpa only [markedMemoryNormalizedEndpointWeight,markedMemoryIndependentEndpointScalar_eq,
    markedMemoryNormalizedHistoryAssembly,markedMemoryFiniteHistoryAssembly,markedMemoryHistoryTransport] using
      (markedMemoryIndependent_source_lifespan_weight hZ (markedMemoryFiniteTableau_toIndependent hZ f)
        order ψ η d₀ Y Q χ ν V q).symm

end
end ArtinMatthews
