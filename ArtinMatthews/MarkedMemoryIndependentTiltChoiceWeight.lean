module

public import ArtinMatthews.MarkedMemoryIndependentChoiceProduct
public import ArtinMatthews.MarkedMemoryTiltRescale
public import ArtinMatthews.MarkedMemoryBoundaryRescale
public import ArtinMatthews.MarkedMemoryChronologicalRescale
public import ArtinMatthews.MarkedMemoryIndependentChoiceWeight
public import ArtinMatthews.MarkedMemoryTiltEndpointSum
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

/-! The actual tilted source/history coefficient is the exact primewise
choice product times the original physical V normalization and ordered
raw-edge residual. Initial atoms remain outside chronological W. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (hempty : ∀ j,(d.lifespan j).initial=[])

include hempty in
theorem markedMemoryIndependent_source_mass_rescale
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (hV : ∀ j,V j≠0) :
    markedRawStateMass ν (markedMemoryIndependentState hZ d 0 (Nat.zero_le n))=
      (∏ j,(V j)⁻¹)^(pads+1)*
        markedRawStateMass (markedMemoryScaledAtoms ν V) (markedMemoryIndependentState hZ d 0 (Nat.zero_le n)) := by
  rw [markedMemoryInitialIdentityMass_source hZ d hempty ν,
    markedMemoryInitialIdentityMass_source hZ d hempty (markedMemoryScaledAtoms ν V),
    markedMemoryInitialIdentityMass_eq hZ d hempty ν,
    markedMemoryInitialIdentityMass_eq hZ d hempty (markedMemoryScaledAtoms ν V)]
  exact markedMemoryRawActiveMass_rescale ν V hV _

variable (hinj : Function.Injective (markedMemoryIndependentPrime hZ d))
  (hterminal : ∀ j,markedMemoryIndependentQueue hZ d (2*n+1) j=[])
  (hn : MarkedMemoryBirthNormalized hZ d)
  (order : Fin n → J → Equiv.Perm (Fin pads))
  (ha : MarkedMemoryHistoryAnchorAdmissible hZ (markedMemoryIndependentHistory hZ d order))
  (V : J → ℝ) (hV : ∀ j,V j≠0) (q : ℝ)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
  (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)

local notation "H" => markedMemoryIndependentHistory hZ d order
local notation "ν" => markedMemoryTiltAtoms (P := P) V q n
local notation "atom" => markedMemoryLineAtoms (P := P) q n
local notation "s" => markedMemoryIndependentState hZ d 0 (Nat.zero_le n)
local notation "C" => ((∏ j,(V j)⁻¹:ℝ):ℂ)

include hinj hempty hterminal hn ha hV in
theorem markedMemoryIndependent_tilt_choice_source_weight :
    (markedRawStateMass ν s:ℂ)*
      markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q 1 (markedMemoryHistoryVisitSchedule q n) χ n 0 H=
      (markedPhysicalMass V (pads+1):ℂ)*C^n*
        ((markedMemoryIndependentPrimeChoiceProduct hZ d hinj q atom/
          markedMemoryIndependentBirthFactorials hZ d:ℝ):ℂ)*
            markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n 0 H := by
  have hs := markedMemoryIndependent_source_mass_rescale hZ d hempty ν V hV
  rw [markedMemoryScaledAtoms_tilt V hV q n] at hs
  have hw := markedMemoryChronologicalWeight_rescale ν V hV hZ ψ η d₀ Y Q 1
    (markedMemoryHistoryVisitSchedule q n) χ n 0 H
  rw [markedMemoryScaledAtoms_tilt V hV q n] at hw
  rw [hs,hw]
  simp only [Complex.ofReal_mul,Complex.ofReal_pow]
  calc
    _ = C^(pads+1+n)*((markedRawStateMass atom s:ℂ)*
        markedMemoryChronologicalWeight atom (fun _ => 1) hZ ψ η d₀ Y Q 1
          (markedMemoryHistoryVisitSchedule q n) χ n 0 H) := by
      rw [pow_add]
      ring
    _ = C^(pads+1+n)*
        ((markedMemoryIndependentPrimeChoiceProduct hZ d hinj q atom/
          markedMemoryIndependentBirthFactorials hZ d:ℝ):ℂ)*
            markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n 0 H := by
      rw [markedMemoryIndependent_choice_source_weight hZ d hinj hempty hterminal hn order ha atom q ψ η d₀ Y Q χ]
      ring
    _ = _ := by
      rw [markedMemoryPhysicalPathNormalization V (pads+1) n]

end
end ArtinMatthews
