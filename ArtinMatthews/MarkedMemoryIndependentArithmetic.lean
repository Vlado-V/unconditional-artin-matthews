module

public import ArtinMatthews.MarkedMemoryHistoryArithmetic
public import ArtinMatthews.MarkedMemoryIndependentChoiceProduct
public import ArtinMatthews.MarkedMemoryTiltRescale
public import ArtinMatthews.MarkedMemoryHistoryRunPowers
public import ArtinMatthews.MarkedMemoryIndependentCorrespondenceGroup
public import ArtinMatthews.MarkedMemoryIndependentRunFiber
public import ArtinMatthews.MarkedMemoryIndependentTiltChoiceWeight
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Pure arithmetic identities for the actual independent tableau. These
hold before choosing any edge kernel, including at its zeros. The source
supplies the initial atoms; the physical V normalization is explicit. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (order : Fin n → J → Equiv.Perm (Fin pads))

theorem markedMemoryIndependent_primeMass
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) :
    markedMemoryHistoryPrimeMass ν V hZ (markedMemoryIndependentHistory hZ d order)=
      ∏ a : Σ j,A j,markedMemoryIndependentBirthMass hZ d ν V a *
        (V a.1)⁻¹ ^ markedMemoryIndependentRunCount hZ d a := by
  rw [markedMemoryHistoryPrimeMass_lifespans]
  simp_rw [markedMemoryHistoryRunMass_pow]
  rw [← Equiv.prod_comp (markedMemoryIndependentAddressEquiv hZ d order).symm]
  apply Finset.prod_congr rfl
  intro a _
  rw [markedMemoryIndependent_birthMass hZ d order ν V,
    (markedMemoryIndependentAddressEquiv hZ d order).apply_symm_apply,
    markedMemoryIndependent_runCount]
  have hg := markedMemoryIndependentAddress_group hZ d order
    ((markedMemoryIndependentAddressEquiv hZ d order).symm a)
  rw [(markedMemoryIndependentAddressEquiv hZ d order).apply_symm_apply] at hg
  rw [← hg]

theorem markedMemoryIndependent_arithmetic
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (q : ℝ) :
    markedMemoryHistoryArithmeticWeight ν V hZ (markedMemoryHistoryVisitSchedule q n) 0
      (markedMemoryIndependentHistory hZ d order)=
      (∏ a : Σ j,A j,markedMemoryIndependentBirthMass hZ d ν V a *
        (V a.1)⁻¹ ^ markedMemoryIndependentRunCount hZ d a *
        markedMemoryIndependentEndpointScalar hZ d q a) /
          markedMemoryIndependentBirthFactorials hZ d := by
  have hg : markedMemoryHistoryGhostScalarProduct hZ (markedMemoryIndependentHistory hZ d order)
      (markedMemoryHistoryVisitSchedule q n) 0=
      ∏ a : Σ j,A j,markedMemoryIndependentLifespanScalar hZ d
        (markedMemoryHistoryVisitSchedule q n) 0 a := by
    rw [markedMemoryHistoryGhostScalarProduct_lifespans,
      ← Equiv.prod_comp (markedMemoryIndependentAddressEquiv hZ d order).symm]
    exact Finset.prod_congr rfl (fun a _ => markedMemoryIndependent_lifespanScalar hZ d order
      (markedMemoryHistoryVisitSchedule q n) 0 a)
  rw [markedMemoryHistoryArithmeticWeight,markedMemoryIndependent_primeMass,hg,
    markedMemoryIndependent_birthFactorials]
  simp_rw [markedMemoryIndependentLifespanScalar_source,← markedMemoryIndependentEndpointScalar_eq]
  simp only [Finset.prod_mul_distrib]
  ring

variable (hinj : Function.Injective (markedMemoryIndependentPrime hZ d))
  (hempty : ∀ j,(d.lifespan j).initial=[])
  (hterminal : ∀ j,markedMemoryIndependentQueue hZ d (2*n+1) j=[])
  (hn : MarkedMemoryBirthNormalized hZ d)
  (ha : MarkedMemoryHistoryAnchorAdmissible hZ (markedMemoryIndependentHistory hZ d order))

include hempty in
theorem markedMemoryIndependent_unit_source_arithmetic
    (atom : (j : J) → ↥(P j) → ℝ) (q : ℝ) :
    markedRawStateMass atom (markedMemoryIndependentState hZ d 0 (Nat.zero_le n)) *
      markedMemoryHistoryArithmeticWeight atom (fun _ => 1) hZ
        (markedMemoryHistoryVisitSchedule q n) 0 (markedMemoryIndependentHistory hZ d order)=
      (∏ a : Σ j,A j,atom a.1 (d.particle a.1 a.2).1 *
        markedMemoryIndependentEndpointScalar hZ d q a) /
          markedMemoryIndependentBirthFactorials hZ d := by
  rw [markedMemoryIndependent_arithmetic]
  simp only [inv_one,one_pow,mul_one]
  rw [← mul_div_assoc]
  have hp := markedMemory_source_birth_product hZ d hempty atom (fun _ => 1)
    (markedMemoryIndependentEndpointScalar hZ d q)
  simpa only [markedMemoryCompletedBirthMass,ite_self,one_mul] using
    congrArg (fun a : ℝ => a / markedMemoryIndependentBirthFactorials hZ d) hp

include hinj hempty hterminal hn ha in
theorem markedMemoryIndependent_choice_source_arithmetic
    (atom : (j : J) → ↥(P j) → ℝ) (q : ℝ) :
    markedRawStateMass atom (markedMemoryIndependentState hZ d 0 (Nat.zero_le n)) *
      markedMemoryHistoryArithmeticWeight atom (fun _ => 1) hZ
        (markedMemoryHistoryVisitSchedule q n) 0 (markedMemoryIndependentHistory hZ d order)=
      markedMemoryIndependentPrimeChoiceProduct hZ d hinj q atom /
        markedMemoryIndependentBirthFactorials hZ d := by
  rw [markedMemoryIndependent_unit_source_arithmetic hZ d order hempty,
    markedMemoryIndependentPrimeChoiceProduct_eq hZ d hinj hempty hterminal hn order ha]

include hinj hempty hterminal hn ha in
theorem markedMemoryIndependent_tilt_source_arithmetic
    (V : J → ℝ) (hV : ∀ j,V j≠0) (q : ℝ) :
    markedRawStateMass (markedMemoryTiltAtoms (P := P) V q n)
        (markedMemoryIndependentState hZ d 0 (Nat.zero_le n)) *
      markedMemoryHistoryArithmeticWeight (markedMemoryTiltAtoms (P := P) V q n) V hZ
        (markedMemoryHistoryVisitSchedule q n) 0 (markedMemoryIndependentHistory hZ d order)=
      markedPhysicalMass V (pads+1) * (∏ j,(V j)⁻¹)^n *
        (markedMemoryIndependentPrimeChoiceProduct hZ d hinj q (markedMemoryLineAtoms (P := P) q n) /
          markedMemoryIndependentBirthFactorials hZ d) := by
  rw [markedMemoryIndependent_source_mass_rescale hZ d hempty _ V hV,
    markedMemoryHistoryArithmeticWeight_rescale _ V hZ hV,
    markedMemoryScaledAtoms_tilt V hV]
  calc
    _ = (∏ j,(V j)⁻¹)^(pads+1+n) *
        (markedRawStateMass (markedMemoryLineAtoms (P := P) q n)
          (markedMemoryIndependentState hZ d 0 (Nat.zero_le n)) *
          markedMemoryHistoryArithmeticWeight (markedMemoryLineAtoms (P := P) q n) (fun _ => 1) hZ
            (markedMemoryHistoryVisitSchedule q n) 0 (markedMemoryIndependentHistory hZ d order)) := by
      rw [pow_add]
      ring
    _ = _ := by
      rw [markedMemoryIndependent_choice_source_arithmetic hZ d order hinj hempty hterminal hn ha]
      rw [pow_add]
      have hp : (∏ j,(V j)⁻¹)^(pads+1)=markedPhysicalMass V (pads+1) := by
        simp only [markedPhysicalMass,Finset.prod_pow]
      rw [hp]

end
end ArtinMatthews
