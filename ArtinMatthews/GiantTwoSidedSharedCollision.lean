module

public import ArtinMatthews.MarkedPhysicalPadCollisionMass
public import ArtinMatthews.DivisorBound
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

/-! The exceptional shared lists repeat a label or hit an actual prime
divisor of the two stripped positions. Their normalized harmonic mass
is bounded by the checked finite pad estimate. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def giantTwoSidedSharedForbidden (P : Finset ℕ) (n : ℕ) : Finset ↥P :=
  univ.filter (fun p => (p:ℕ) ∣ n)

def GiantTwoSidedSharedGood {J : Type*} {P : J → Finset ℕ} {k : ℕ}
    (c : MarkedPhysicalMarking P k) (w : ℕ) : Prop :=
  MarkedPhysicalMarkingDistinct c ∧ ∀ j l,¬(c j l:ℕ) ∣ w*(w+1)

def giantTwoSidedSharedBadMass {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (k w : ℕ) : ℝ :=
  markedEventMass (markedPhysicalPadHarmonicMass P k) (fun c => ¬GiantTwoSidedSharedGood c w)

theorem giantTwoSidedSharedGood_complement {J : Type*} {P : J → Finset ℕ} {k : ℕ}
    (c : MarkedPhysicalMarking P k) (w : ℕ) :
    ¬GiantTwoSidedSharedGood c w ↔
      ∃ j,MarkedPadCollision (giantTwoSidedSharedForbidden (P j) (w*(w+1))) (c j) := by
  classical
  constructor
  · intro hn
    by_contra hbad
    apply hn
    refine ⟨?_,?_⟩
    · intro j i l he
      by_contra hne
      exact hbad ⟨j,Or.inl ⟨i,l,hne,he⟩⟩
    · intro j l hd
      exact hbad ⟨j,Or.inr ⟨l,mem_filter.mpr ⟨mem_univ _,hd⟩⟩⟩
  · rintro ⟨j,h⟩ hg
    rcases h with ⟨i,l,hne,he⟩ | ⟨l,hd⟩
    · exact hne (hg.1 j he)
    · exact hg.2 j l (mem_filter.mp hd).2

theorem giantTwoSidedSharedForbidden_card_le (P : Finset ℕ) (hP : ∀ p∈P,p.Prime)
    {n : ℕ} (hn : 0 < n) :
    ((giantTwoSidedSharedForbidden P n).card:ℝ) ≤ Real.log (n:ℝ)/Real.log (3/2) := by
  let S := giantTwoSidedSharedForbidden P n
  let T := S.image Subtype.val
  have hcard : T.card=S.card := card_image_of_injective S Subtype.val_injective
  rw [← hcard]
  apply card_le_log_div_log_of_primes_dvd hn (by norm_num)
  · intro p hp
    obtain ⟨q,_,rfl⟩ := mem_image.mp hp
    exact hP q.val q.property
  · intro p hp
    obtain ⟨q,_,rfl⟩ := mem_image.mp hp
    exact (by norm_num : (3/2:ℝ)<2).trans_le (Nat.cast_le.mpr (hP q.val q.property).two_le)
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hp
    exact (mem_filter.mp hq).2

theorem giantTwoSidedSharedCollision_group_mass {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (k : ℕ) (hV : ∀ j,0 < bandReciprocalMass (P j))
    (A : (j : J) → Finset ↥(P j)) (j : J) :
    markedEventMass (markedPhysicalPadHarmonicMass P k) (fun c => MarkedPadCollision (A j) (c j)) =
      markedEventMass (finiteProductMass (fun _ : Fin k => markedHarmonicAtom (P j)))
        (MarkedPadCollision (A j)) := by
  classical
  let μ := fun j : J => fun c : Fin k → ↥(P j) => ∏ l,markedHarmonicAtom (P j) (c l)
  let f := fun j : J => fun c : Fin k → ↥(P j) => if MarkedPadCollision (A j) c then (1:ℝ) else 0
  have hμ (j : J) : (∑ c : Fin k → ↥(P j),μ j c)=1 := by
    dsimp only [μ]
    rw [← Fintype.prod_sum (fun (_l : Fin k) (p : ↥(P j)) => markedHarmonicAtom (P j) p)]
    simp_rw [markedHarmonicAtom_sum (P j) (hV j)]
    simp
  simpa only [markedEventMass,markedPhysicalPadHarmonicMass,finiteProductMass,μ,f] using
    finiteProduct_expectation_coordinate μ f hμ j

theorem giantTwoSidedSharedBadMass_le {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime)
    (hV : ∀ j,0 < bandReciprocalMass (P j))
    (k w : ℕ) (hw : 0 < w) {y : ℝ} (hy : 0 < y)
    (hlarge : ∀ j p,p∈P j → y ≤ (p:ℝ)) :
    giantTwoSidedSharedBadMass P k w ≤
      ((k:ℝ)^2+(k:ℝ)*(Real.log ((w*(w+1):ℕ):ℝ)/Real.log (3/2))) *
        ∑ j,1/(y*bandReciprocalMass (P j)) := by
  let A (j : J) := giantTwoSidedSharedForbidden (P j) (w*(w+1))
  let μ := markedPhysicalPadHarmonicMass P k
  have hA (j : J) : ((A j).card:ℝ) ≤ Real.log ((w*(w+1):ℕ):ℝ)/Real.log (3/2) :=
    giantTwoSidedSharedForbidden_card_le (P j) (hP j) (Nat.mul_pos hw (Nat.succ_pos _))
  have hμ := markedPhysicalPadHarmonicMass_nonneg P k hV
  calc
    _ = markedEventMass μ (fun c => ∃ j,MarkedPadCollision (A j) (c j)) := by
      unfold giantTwoSidedSharedBadMass
      simp only [giantTwoSidedSharedGood_complement,A,μ]
    _ ≤ ∑ j,markedEventMass μ (fun c => MarkedPadCollision (A j) (c j)) :=
      markedEventMass_exists_le μ hμ (fun j c => MarkedPadCollision (A j) (c j))
    _ ≤ _ := by
      rw [Finset.mul_sum]
      apply sum_le_sum
      intro j _
      rw [giantTwoSidedSharedCollision_group_mass P k hV A j]
      apply (marked_harmonic_pad_collision_bound (P j) (hV j) hy (hlarge j) k (A j)).trans
      apply mul_le_mul_of_nonneg_right _ (one_div_nonneg.mpr (mul_nonneg hy.le (hV j).le))
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hA j) (Nat.cast_nonneg k))

end
end ArtinMatthews
