module

public import ArtinMatthews.GiantTwoSidedActiveClass
public import ArtinMatthews.GiantTwoSidedActiveModulus
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

/-! The concrete active modulus and canonical root residue use the
same distinct-prime set. Compatibility is tested on the actual label
path; an incompatible path has no contribution from any Nat root. -/
namespace ArtinMatthews
open Finset
noncomputable section

theorem giantTwoSidedPathUsed_prime {J ι : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime) {M : ℕ}
    (I : Finset ι) (labels : ι → MarkedPhysicalMarking P M) :
    ∀ p∈markedPhysicalPathUsedPrimes I labels,p.Prime := by
  intro p hp
  obtain ⟨j,_,hj⟩ := mem_biUnion.mp (markedPhysicalPathUsedPrimes_subset I labels hp)
  exact hP j p hj

def giantTwoSidedRootClass {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime) {M n : ℕ}
    (labels : Fin (n+1) → MarkedPhysicalMarking P M) (offset : Fin (n+1) → ℤ) : ℕ :=
  giantTwoSidedCRTResidue (markedPhysicalPathUsedPrimes univ labels)
    (giantTwoSidedPathUsed_prime hP univ labels) (giantTwoSidedActiveResidue univ labels offset)

theorem giantTwoSidedActiveRoot_iff_class {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime) {M n : ℕ}
    (labels : Fin (n+1) → MarkedPhysicalMarking P M) (offset : Fin (n+1) → ℤ)
    (hc : GiantTwoSidedActiveCompatible univ labels offset) (root : ℕ) :
    GiantTwoSidedActiveRoot univ labels offset root ↔
      Nat.ModEq (giantTwoSidedActiveModulus labels) root (giantTwoSidedRootClass hP labels offset) := by
  rw [giantTwoSidedActiveRoot_iff_residues univ labels offset hc]
  exact (giantTwoSidedCRTResidue_iff (markedPhysicalPathUsedPrimes univ labels)
    (giantTwoSidedPathUsed_prime hP univ labels) (giantTwoSidedActiveResidue univ labels offset) root).symm

end
end ArtinMatthews
