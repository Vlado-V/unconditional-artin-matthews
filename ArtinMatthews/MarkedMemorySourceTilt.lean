module

public import ArtinMatthews.MarkedMemoryInitialMeasure
public import ArtinMatthews.MarkedMemoryNormalizedEndpointWeight
public import ArtinMatthews.MarkedMemoryIndependentWeight
public import ArtinMatthews.MarkedMemoryTiltBasic
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The source measure supplies the initial nu atoms exactly once.
After combining it with the unchanged chronological weight, every
identity has one line/baseline atom and one V inverse per active run. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

def markedMemoryChargedRunCount (a : Σ j,A j) : ℕ :=
  markedMemoryIndependentRunCount hZ d a +
    if (d.lifespan a.1).first a.2 % 2=1 then 0 else 1

def markedMemoryLineBirthAtom (q : ℝ) (N : ℕ) (p : Nat.Primes) : ℝ :=
  1/(((p:ℝ)+1)*markedMemoryBaseline q N p)

theorem markedMemoryCompletedBirthMass_tilt (V : J → ℝ) (hV : ∀ j,V j≠0) (q : ℝ)
    (a : Σ j,A j) :
    markedMemoryCompletedBirthMass hZ d (fun j p => markedMemoryPrimeAtom (V j) q n p.1) V a *
        (V a.1)⁻¹ ^ markedMemoryIndependentRunCount hZ d a =
      (V a.1)⁻¹ ^ markedMemoryChargedRunCount hZ d a *
        markedMemoryLineBirthAtom q n (d.particle a.1 a.2).1.1 := by
  by_cases hg : (d.lifespan a.1).first a.2 % 2=1
  · simpa only [markedMemoryCompletedBirthMass,markedMemoryChargedRunCount,hg,ite_true,
      Nat.add_zero,markedMemoryLineBirthAtom] using
      markedMemory_ghost_run_charge (hV a.1) q n ((d.particle a.1 a.2).1.1 : ℕ)
        (markedMemoryIndependentRunCount hZ d a)
  · simpa only [markedMemoryCompletedBirthMass,markedMemoryChargedRunCount,hg,ite_false,
      one_mul,markedMemoryLineBirthAtom] using
      markedMemory_active_run_charge (V a.1) q n ((d.particle a.1 a.2).1.1 : ℕ)
        (markedMemoryIndependentRunCount hZ d a)

theorem markedMemoryIndependent_source_tilt_weight
    (hempty : ∀ j,(d.lifespan j).initial=[])
    (order : Fin n → J → Equiv.Perm (Fin pads))
    (V : J → ℝ) (hV : ∀ j,V j≠0) (q : ℝ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) :
    (markedRawStateMass (fun j p => markedMemoryPrimeAtom (V j) q n p.1)
      (markedMemoryIndependentState hZ d 0 (Nat.zero_le n)) : ℂ) *
      markedMemoryChronologicalWeight (fun j p => markedMemoryPrimeAtom (V j) q n p.1) V
        hZ ψ η d₀ Y Q 1 (markedMemoryHistoryVisitSchedule q n) χ n 0
          (markedMemoryIndependentHistory hZ d order) =
    (((∏ a : Σ j,A j,
      (V a.1)⁻¹ ^ markedMemoryChargedRunCount hZ d a *
        markedMemoryLineBirthAtom q n (d.particle a.1 a.2).1.1 *
          markedMemoryIndependentEndpointScalar hZ d q a) /
      markedMemoryIndependentBirthFactorials hZ d : ℝ) : ℂ) *
        markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n 0
          (markedMemoryIndependentHistory hZ d order) := by
  let nu : (j : J) → ↥(P j) → ℝ := fun j p => markedMemoryPrimeAtom (V j) q n p.1
  have hp : markedRawStateMass nu (markedMemoryIndependentState hZ d 0 (Nat.zero_le n)) *
      (∏ a : Σ j,A j,markedMemoryIndependentBirthMass hZ d nu V a *
        (V a.1)⁻¹ ^ markedMemoryIndependentRunCount hZ d a *
          markedMemoryIndependentEndpointScalar hZ d q a) =
      ∏ a : Σ j,A j,(V a.1)⁻¹ ^ markedMemoryChargedRunCount hZ d a *
        markedMemoryLineBirthAtom q n (d.particle a.1 a.2).1.1 *
          markedMemoryIndependentEndpointScalar hZ d q a := by
    calc
      _ = ∏ a : Σ j,A j,markedMemoryCompletedBirthMass hZ d nu V a *
          ((V a.1)⁻¹ ^ markedMemoryIndependentRunCount hZ d a *
            markedMemoryIndependentEndpointScalar hZ d q a) := by
        simpa only [mul_assoc] using markedMemory_source_birth_product hZ d hempty nu V
          (fun a => (V a.1)⁻¹ ^ markedMemoryIndependentRunCount hZ d a *
            markedMemoryIndependentEndpointScalar hZ d q a)
      _ = _ := by
        apply Finset.prod_congr rfl
        intro a _
        rw [← mul_assoc,markedMemoryCompletedBirthMass_tilt hZ d V hV q a]
  change (markedRawStateMass nu (markedMemoryIndependentState hZ d 0 (Nat.zero_le n)) : ℂ) * _ = _
  rw [markedMemoryIndependent_source_lifespan_weight]
  simp_rw [← markedMemoryIndependentEndpointScalar_eq]
  calc
    _ = (((markedRawStateMass nu (markedMemoryIndependentState hZ d 0 (Nat.zero_le n)) *
        (∏ a : Σ j,A j,markedMemoryIndependentBirthMass hZ d nu V a *
          (V a.1)⁻¹ ^ markedMemoryIndependentRunCount hZ d a *
            markedMemoryIndependentEndpointScalar hZ d q a)) /
          markedMemoryIndependentBirthFactorials hZ d : ℝ) : ℂ) *
        markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n 0
          (markedMemoryIndependentHistory hZ d order) := by push_cast; ring
    _ = _ := by rw [hp]

end
end ArtinMatthews
