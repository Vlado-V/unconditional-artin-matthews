module

public import ArtinMatthews.GiantCandidateHitSelections
public import Mathlib.Data.Nat.Prime.Defs
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
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! At each selected prime the residue test imposes every listed hit.
Conflicting predecessor and product hits remain an empty event. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

theorem giantCandidateSelectionPrimes_prime {ι : Type*} [Fintype ι]
    {G : ι → Finset ℕ} {k : ι → ℕ} {D : ι → Finset ℕ}
    (hD : D∈giantCandidateHitSelections G k) (hG : ∀ i p,p∈G i → p.Prime) :
    ∀ p∈giantCandidateSelectionPrimes D,p.Prime := by
  intro p hp
  obtain ⟨i,hi⟩ := mem_giantCandidateSelectionPrimes.mp hp
  exact hG i p ((mem_giantCandidateHitSelections.mp hD i).1 hi)

def giantCandidateSelectionPrimeMask {ι : Type*} [Fintype ι]
    (D : ι → Finset ℕ) (side : ι → GiantCandidateHitSide)
    (hP : ∀ p∈giantCandidateSelectionPrimes D,p.Prime)
    (j : ℕ) (p : giantCandidateSelectionPrimes D) : Finset (Fin j → ZMod p.val) := by
  letI : NeZero p.val := ⟨(hP p.val p.property).ne_zero⟩
  exact univ.filter (fun t => ∀ i,p.val∈D i → giantCandidatePrimeResidueHit (side i) t)

theorem mem_giantCandidateSelectionPrimeMask {ι : Type*} [Fintype ι]
    (D : ι → Finset ℕ) (side : ι → GiantCandidateHitSide)
    (hP : ∀ p∈giantCandidateSelectionPrimes D,p.Prime)
    {j : ℕ} (p : giantCandidateSelectionPrimes D) (t : Fin j → ZMod p.val) :
    t∈giantCandidateSelectionPrimeMask D side hP j p ↔
      ∀ i,p.val∈D i → giantCandidatePrimeResidueHit (side i) t := by
  simp only [giantCandidateSelectionPrimeMask,mem_filter,mem_univ,true_and]

theorem giantCandidateSelectedHits_iff_primeMask {ι : Type*} [Fintype ι]
    {G : ι → Finset ℕ} {k : ι → ℕ} {D : ι → Finset ℕ}
    (hD : D∈giantCandidateHitSelections G k) (side : ι → GiantCandidateHitSide)
    (hP : ∀ p∈giantCandidateSelectionPrimes D,p.Prime)
    {j : ℕ} (t : Fin j → ℕ) (ht : 0<∏ i,t i) :
    (∀ i,D i ⊆ giantCandidateHitSet (G i) (side i) (∏ v,t v)) ↔
      ∀ p : giantCandidateSelectionPrimes D,
        (fun i => (t i:ZMod p.val))∈giantCandidateSelectionPrimeMask D side hP j p := by
  constructor
  · intro h p
    apply (mem_giantCandidateSelectionPrimeMask D side hP p _).mpr
    intro i hi
    exact (giantCandidatePrimeHit_iff_residue (side i) p.val t ht).mp (mem_filter.mp (h i hi)).2
  · intro h i p hp
    let q : giantCandidateSelectionPrimes D := ⟨p,mem_giantCandidateSelectionPrimes.mpr ⟨i,hp⟩⟩
    have hr := (mem_giantCandidateSelectionPrimeMask D side hP q _).mp (h q) i hp
    exact mem_filter.mpr ⟨(mem_giantCandidateHitSelections.mp hD i).1 hp,
      (giantCandidatePrimeHit_iff_residue (side i) p t ht).mpr hr⟩

end
end ArtinMatthews
