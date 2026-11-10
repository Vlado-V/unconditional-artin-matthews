module

public import ArtinMatthews.GiantCandidatePrimeResidueModel
public import ArtinMatthews.MarkedPhysicalJointPrimeDamping
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Active path congruences determine one actual CRT class when they
are compatible. The chosen residue is allowed to be a nonunit, and
incompatible active data admit no integer root. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def giantTwoSidedCRTValue (U : Finset ℕ) (hU : ∀ p∈U,p.Prime)
    (r : (p : U) → ZMod p.val) : ZMod (giantCandidateResidueModulus U) :=
  (giantCandidateResidueCRTEquiv U hU).symm r

def giantTwoSidedCRTResidue (U : Finset ℕ) (hU : ∀ p∈U,p.Prime)
    (r : (p : U) → ZMod p.val) : ℕ := (giantTwoSidedCRTValue U hU r).val

theorem giantTwoSidedCRTResidue_iff (U : Finset ℕ) (hU : ∀ p∈U,p.Prime)
    (r : (p : U) → ZMod p.val) (n : ℕ) :
    Nat.ModEq (giantCandidateResidueModulus U) n (giantTwoSidedCRTResidue U hU r) ↔
      ∀ p : U,(n:ZMod p.val)=r p := by
  have hQ : 0<giantCandidateResidueModulus U := prod_pos fun p hp => (hU p hp).pos
  let : NeZero (giantCandidateResidueModulus U) := ⟨hQ.ne'⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  change (n:ZMod (giantCandidateResidueModulus U)) =
    ((giantTwoSidedCRTValue U hU r).val:ZMod (giantCandidateResidueModulus U)) ↔ _
  rw [ZMod.natCast_zmod_val]
  constructor
  · intro hn p
    have h := congrFun (congrArg (giantCandidateResidueCRTEquiv U hU) hn) p
    simpa only [giantTwoSidedCRTValue,RingEquiv.apply_symm_apply,map_natCast,Pi.natCast_apply] using h
  · intro hn
    apply (giantCandidateResidueCRTEquiv U hU).injective
    rw [giantTwoSidedCRTValue,RingEquiv.apply_symm_apply]
    funext p
    simpa only [map_natCast,Pi.natCast_apply] using hn p

def giantTwoSidedActiveVisit {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}
    (I : Finset ι) (labels : ι → MarkedPhysicalMarking P M)
    (p : ↥(markedPhysicalPathUsedPrimes I labels)) : ↥I :=
  ⟨Classical.choose (mem_biUnion.mp p.property),
    (Classical.choose_spec (mem_biUnion.mp p.property)).1⟩

theorem giantTwoSidedActiveVisit_mem {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}
    (I : Finset ι) (labels : ι → MarkedPhysicalMarking P M)
    (p : ↥(markedPhysicalPathUsedPrimes I labels)) :
    p.val∈markedPhysicalActivePrimes (labels (giantTwoSidedActiveVisit I labels p).val) :=
  (Classical.choose_spec (mem_biUnion.mp p.property)).2

def giantTwoSidedActiveResidue {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}
    (I : Finset ι) (labels : ι → MarkedPhysicalMarking P M) (offset : ι → ℤ)
    (p : ↥(markedPhysicalPathUsedPrimes I labels)) : ZMod p.val :=
  -(offset (giantTwoSidedActiveVisit I labels p).val:ZMod p.val)

def GiantTwoSidedActiveCompatible {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}
    (I : Finset ι) (labels : ι → MarkedPhysicalMarking P M) (offset : ι → ℤ) : Prop :=
  ∀ p : ↥(markedPhysicalPathUsedPrimes I labels),∀ v∈I,p.val∈markedPhysicalActivePrimes (labels v) →
    (offset v:ZMod p.val)=(offset (giantTwoSidedActiveVisit I labels p).val:ZMod p.val)

def GiantTwoSidedActiveRoot {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}
    (I : Finset ι) (labels : ι → MarkedPhysicalMarking P M) (offset : ι → ℤ) (n : ℕ) : Prop :=
  ∀ v∈I,∀ p∈markedPhysicalActivePrimes (labels v),(p:ℤ)∣(n:ℤ)+offset v

theorem giantTwoSidedActiveRoot_compatible {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}
    (I : Finset ι) (labels : ι → MarkedPhysicalMarking P M) (offset : ι → ℤ) {n : ℕ}
    (hn : GiantTwoSidedActiveRoot I labels offset n) : GiantTwoSidedActiveCompatible I labels offset := by
  intro p v hv hp
  have h₁ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p.val).mpr (hn v hv p.val hp)
  have h₂ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p.val).mpr
    (hn _ (giantTwoSidedActiveVisit I labels p).property p.val (giantTwoSidedActiveVisit_mem I labels p))
  push_cast at h₁ h₂
  linear_combination h₁-h₂

theorem giantTwoSidedActiveRoot_iff_residues {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}
    (I : Finset ι) (labels : ι → MarkedPhysicalMarking P M) (offset : ι → ℤ)
    (hc : GiantTwoSidedActiveCompatible I labels offset) (n : ℕ) :
    GiantTwoSidedActiveRoot I labels offset n ↔
      ∀ p : ↥(markedPhysicalPathUsedPrimes I labels),(n:ZMod p.val)=giantTwoSidedActiveResidue I labels offset p := by
  constructor
  · intro hn p
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p.val).mpr
      (hn _ (giantTwoSidedActiveVisit I labels p).property p.val (giantTwoSidedActiveVisit_mem I labels p))
    push_cast at hz
    unfold giantTwoSidedActiveResidue
    linear_combination hz
  · intro hn v hv p hp
    let p' : ↥(markedPhysicalPathUsedPrimes I labels) := ⟨p,mem_biUnion.mpr ⟨v,hv,hp⟩⟩
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    push_cast
    rw [hc p' v hv hp,hn p']
    exact neg_add_cancel _

theorem giantTwoSidedActiveRoot_impossible {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}
    (I : Finset ι) (labels : ι → MarkedPhysicalMarking P M) (offset : ι → ℤ)
    (hc : ¬GiantTwoSidedActiveCompatible I labels offset) (n : ℕ) :
    ¬GiantTwoSidedActiveRoot I labels offset n := fun hn => hc (giantTwoSidedActiveRoot_compatible I labels offset hn)

end
end ArtinMatthews
