module

public import ArtinMatthews.MarkedPhysicalPrimeHitProduct
public import ArtinMatthews.GiantTwoSidedEndpointStates
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

/-! Full independent prime-residue positions, with the original ordered
distinct markings and the original constant list mass. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev GiantTwoSidedFullResidue {J : Type*} [Fintype J] (P : J → Finset ℕ) :=
  (p : ↥(markedPhysicalBandPrimes P)) → ZMod p.val

def giantTwoSidedResidueIndex {J : Type*} [Fintype J] {P : J → Finset ℕ}
    (j : J) (p : ↥(P j)) : ↥(markedPhysicalBandPrimes P) :=
  ⟨p.val,mem_biUnion.mpr ⟨j,mem_univ j,p.property⟩⟩

abbrev GiantTwoSidedResidueState {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (M : ℕ) :=
  {s : GiantTwoSidedFullResidue P × MarkedPhysicalMarking P M //
    MarkedPhysicalMarkingDistinct s.2 ∧
      ∀ j i,s.1 (giantTwoSidedResidueIndex j (s.2 j i))=0}

def giantTwoSidedResidueTranslate {J : Type*} [Fintype J] {P : J → Finset ℕ}
    (h : ℤ) (r : GiantTwoSidedFullResidue P) : GiantTwoSidedFullResidue P :=
  fun p => r p+(h : ZMod p.val)

theorem giantTwoSidedResidueTranslate_neg {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (h : ℤ) (r : GiantTwoSidedFullResidue P) :
    giantTwoSidedResidueTranslate (-h) (giantTwoSidedResidueTranslate h r)=r := by
  funext p
  simp [giantTwoSidedResidueTranslate]

def giantTwoSidedResidueZeros {J : Type*} [Fintype J] {P : J → Finset ℕ}
    (r : GiantTwoSidedFullResidue P) : Finset ℕ :=
  (markedPhysicalBandPrimes P).attach.filter (fun p => r p=0) |>.image Subtype.val

theorem mem_giantTwoSidedResidueZeros {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (r : GiantTwoSidedFullResidue P) (p : ↥(markedPhysicalBandPrimes P)) :
    p.val∈giantTwoSidedResidueZeros r ↔ r p=0 := by
  simp only [giantTwoSidedResidueZeros,mem_image,mem_filter,mem_attach,true_and]
  constructor
  · rintro ⟨q,hq,hqp⟩
    have heq : q=p := Subtype.ext hqp
    exact heq ▸ hq
  · intro hp
    exact ⟨p,hp,rfl⟩

theorem giantTwoSidedResidueZeros_subset {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (r : GiantTwoSidedFullResidue P) :
    giantTwoSidedResidueZeros r ⊆ markedPhysicalBandPrimes P := by
  intro p hp
  obtain ⟨q,_,rfl⟩ := mem_image.mp hp
  exact q.property

def giantTwoSidedResidueZeroProduct {J : Type*} [Fintype J] {P : J → Finset ℕ}
    (r : GiantTwoSidedFullResidue P) : ℕ := ∏ p∈giantTwoSidedResidueZeros r,p

theorem giantTwoSidedResidueZeroProduct_dvd_iff {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (r : GiantTwoSidedFullResidue P) (p : ↥(markedPhysicalBandPrimes P)) :
    p.val ∣ giantTwoSidedResidueZeroProduct r ↔ r p=0 := by
  have hp : p.val.Prime := by
    obtain ⟨j,_,hj⟩ := mem_biUnion.mp p.property
    exact hP j p.val hj
  rw [← mem_giantTwoSidedResidueZeros r p]
  constructor
  · intro hd
    obtain ⟨q,hq,hdq⟩ := (hp.prime.dvd_finsetProd_iff fun q => q).mp hd
    have hqprime : q.Prime := by
      obtain ⟨j,_,hj⟩ := mem_biUnion.mp (giantTwoSidedResidueZeros_subset r hq)
      exact hP j q hj
    have heq : p.val=q := (Nat.dvd_prime hqprime).mp hdq |>.resolve_left hp.ne_one
    simpa only [heq] using hq
  · intro hpz
    exact dvd_prod_of_mem (fun p : ℕ => p) hpz

theorem giantTwoSidedResidueZeroProduct_active {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (r : GiantTwoSidedFullResidue P) :
    activeDivisors (markedPhysicalBandPrimes P) (giantTwoSidedResidueZeroProduct r)=
      giantTwoSidedResidueZeros r := by
  ext p
  constructor
  · intro hp
    have h := mem_filter.mp hp
    exact (mem_giantTwoSidedResidueZeros r ⟨p,h.1⟩).mpr
      ((giantTwoSidedResidueZeroProduct_dvd_iff hP r ⟨p,h.1⟩).mp h.2)
  · intro hp
    have hband := giantTwoSidedResidueZeros_subset r hp
    exact mem_filter.mpr ⟨hband,(giantTwoSidedResidueZeroProduct_dvd_iff hP r ⟨p,hband⟩).mpr
      ((mem_giantTwoSidedResidueZeros r ⟨p,hband⟩).mp hp)⟩

def giantTwoSidedResidueDamping {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (M : ℕ) (q : ℝ) (r : GiantTwoSidedFullResidue P) : ℝ :=
  q^((((giantTwoSidedResidueZeros r).card-M*Fintype.card J:ℕ):ℝ)/2)

theorem giantTwoSidedResidueDamping_eq_physical {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (M : ℕ) (q : ℝ) (r : GiantTwoSidedFullResidue P) :
    giantTwoSidedResidueDamping P M q r=
      giantTwoSidedEndpointDamping P M q (giantTwoSidedResidueZeroProduct r) := by
  simp only [giantTwoSidedResidueDamping,giantTwoSidedEndpointDamping,bandCount,
    ← giantTwoSidedResidueZeroProduct_active hP r,markedPhysicalBandPrimes]

theorem giantTwoSidedResidueDamping_mem_unitInterval {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (M : ℕ) {q : ℝ} (hq : q∈Set.Icc (0:ℝ) 1)
    (r : GiantTwoSidedFullResidue P) :
    giantTwoSidedResidueDamping P M q r∈Set.Icc (0:ℝ) 1 := by
  exact ⟨Real.rpow_nonneg hq.1 _,Real.rpow_le_one hq.1 hq.2 (by positivity)⟩

def giantTwoSidedResiduePermute {J : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}
    (π : J → Equiv.Perm (Fin M)) :
    GiantTwoSidedResidueState P M ≃ GiantTwoSidedResidueState P M where
  toFun s := ⟨(s.val.1,fun j l => s.val.2 j (π j l)),
    fun j => (s.property.1 j).comp (π j).injective,
    fun j l => s.property.2 j (π j l)⟩
  invFun s := ⟨(s.val.1,fun j l => s.val.2 j ((π j).symm l)),
    fun j => (s.property.1 j).comp (π j).symm.injective,
    fun j l => s.property.2 j ((π j).symm l)⟩
  left_inv s := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext j l
      exact congrArg (s.val.2 j) ((π j).apply_symm_apply l)
  right_inv s := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext j l
      exact congrArg (s.val.2 j) ((π j).symm_apply_apply l)

def giantTwoSidedResidueHaarStateMass {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (M : ℕ) : ℝ :=
  markedPhysicalMass (fun j => bandReciprocalMass (P j)) M /
    (∏ p∈markedPhysicalBandPrimes P,p:ℕ)

end
end ArtinMatthews
