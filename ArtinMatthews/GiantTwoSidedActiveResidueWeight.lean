module

public import ArtinMatthews.GiantTwoSidedActiveClass
public import ArtinMatthews.GiantTwoSidedResidueLoss
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

/-! On the forced active class, every used-prime damping factor is
determined by the actual offsets. Unused primes retain their complete
repeated-offset loss. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def giantTwoSidedIntegerPrimePath {J ι : Type*} [Fintype J]
    {P : J → Finset ℕ} {M : ℕ} (I : Finset ι)
    (labels : ι → MarkedPhysicalMarking P M) (r : ι → ℝ) (offset : ι → ℤ)
    (root : ℕ) (p : ℕ) : ℝ :=
  ∏ v∈I,if p∈markedPhysicalActivePrimes (labels v) then 1
    else if (p:ℤ)∣(root:ℤ)+offset v then r v else 1

def giantTwoSidedActiveResidueWeight {J ι : Type*} [Fintype J]
    {P : J → Finset ℕ} {M : ℕ} (I : Finset ι)
    (labels : ι → MarkedPhysicalMarking P M) (r : ι → ℝ) (offset : ι → ℤ) : ℝ :=
  ∏ p : ↥(markedPhysicalPathUsedPrimes I labels),∏ v∈I,
    if p.val∈markedPhysicalActivePrimes (labels v) then 1 else
      if (offset v:ZMod p.val)=(offset (giantTwoSidedActiveVisit I labels p).val:ZMod p.val)
        then r v else 1

theorem giantTwoSidedActiveRoot_offset_iff {J ι : Type*} [Fintype J]
    {P : J → Finset ℕ} {M : ℕ} (I : Finset ι)
    (labels : ι → MarkedPhysicalMarking P M) (offset : ι → ℤ) {root : ℕ}
    (hroot : GiantTwoSidedActiveRoot I labels offset root)
    (p : ↥(markedPhysicalPathUsedPrimes I labels)) (v : ι) :
    (p.val:ℤ)∣(root:ℤ)+offset v ↔
      (offset v:ZMod p.val)=(offset (giantTwoSidedActiveVisit I labels p).val:ZMod p.val) := by
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p.val).mpr
    (hroot _ (giantTwoSidedActiveVisit I labels p).property p.val (giantTwoSidedActiveVisit_mem I labels p))
  push_cast at hz
  constructor
  · intro hd
    have hv := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p.val).mpr hd
    push_cast at hv
    linear_combination hv-hz
  · intro hv
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p.val).mp
    push_cast
    rw [hv]
    exact hz

theorem giantTwoSidedIntegerPrimePath_used {J ι : Type*} [Fintype J]
    {P : J → Finset ℕ} {M : ℕ} (I : Finset ι)
    (labels : ι → MarkedPhysicalMarking P M) (r : ι → ℝ) (offset : ι → ℤ) {root : ℕ}
    (hroot : GiantTwoSidedActiveRoot I labels offset root) :
    (∏ p∈markedPhysicalPathUsedPrimes I labels,
      giantTwoSidedIntegerPrimePath I labels r offset root p) =
        giantTwoSidedActiveResidueWeight I labels r offset := by
  rw [← prod_coe_sort]
  unfold giantTwoSidedActiveResidueWeight giantTwoSidedIntegerPrimePath
  apply prod_congr rfl
  intro p _
  apply prod_congr rfl
  intro v _
  simp only [giantTwoSidedActiveRoot_offset_iff I labels offset hroot p v]

theorem giantTwoSidedIntegerPrimePath_unused {J ι : Type*} [Fintype J]
    {P : J → Finset ℕ} {M : ℕ} (I : Finset ι)
    (labels : ι → MarkedPhysicalMarking P M) (r : ι → ℝ) (offset : ι → ℤ)
    (root p : ℕ) (hp : p∉markedPhysicalPathUsedPrimes I labels) :
    giantTwoSidedIntegerPrimePath I labels r offset root p =
      1-giantTwoSidedResidueLossNat I r offset p (root%p) := by
  rw [giantTwoSidedResidueLossNat_eq_offset_product]
  unfold giantTwoSidedIntegerPrimePath
  apply prod_congr rfl
  intro v hv
  exact ite_eq_right (fun ha => hp (mem_biUnion.mpr ⟨v,hv,ha⟩))

theorem giantTwoSidedIntegerPrimePath_forced_split {J ι : Type*} [Fintype J]
    {P : J → Finset ℕ} {M : ℕ} (I : Finset ι)
    (labels : ι → MarkedPhysicalMarking P M) (r : ι → ℝ) (offset : ι → ℤ) {root : ℕ}
    (hroot : GiantTwoSidedActiveRoot I labels offset root) :
    (∏ p∈markedPhysicalBandPrimes P,giantTwoSidedIntegerPrimePath I labels r offset root p) =
      giantTwoSidedActiveResidueWeight I labels r offset *
        ∏ p∈markedPhysicalBandPrimes P \ markedPhysicalPathUsedPrimes I labels,
          (1-giantTwoSidedResidueLossNat I r offset p (root%p)) := by
  have hs := prod_sdiff (f:=giantTwoSidedIntegerPrimePath I labels r offset root)
    (markedPhysicalPathUsedPrimes_subset I labels)
  rw [mul_comm] at hs
  rw [← hs,giantTwoSidedIntegerPrimePath_used I labels r offset hroot]
  congr 1
  apply prod_congr rfl
  intro p hp
  exact giantTwoSidedIntegerPrimePath_unused I labels r offset root p (mem_sdiff.mp hp).2

end
end ArtinMatthews
