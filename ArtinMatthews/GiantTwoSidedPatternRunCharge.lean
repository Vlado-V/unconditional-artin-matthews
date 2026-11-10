module

public import ArtinMatthews.GiantTwoSidedRawSymmetrization
public import ArtinMatthews.GiantTwoSidedPatternCompletions
public import ArtinMatthews.GiantTwoSidedPatternKernel
public import ArtinMatthews.MarkedPhysicalEndpointArithmetic
public import ArtinMatthews.GiantTwoSidedPatternRunCompatibility
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The exact physical band factors assign one inverse reciprocal mass
at each new active run, also after independent slot permutations at
both ends of every chronological edge. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantTwoSidedPattern_active_not_copied_coprime {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) {k ell : ℕ} {C : J → Finset (Fin k)}
    {step : ℤ} {Z Z' : Finset ℕ} {s : GiantTwoSidedEndpointState P (k+ell) Z}
    {t : GiantTwoSidedEndpointState P (k+ell) Z'} {a : GiantTwoSidedPatternAuxiliary P C}
    (h : GiantTwoSidedPatternCondition C step s t a) (j : J) {p : ℕ}
    (hp : p∈markedPhysicalLabelSet s.val.2 j ∨ p∈markedPhysicalLabelSet t.val.2 j)
    (hn : p∉giantTwoSidedPatternCopiedValues (P j) (C j) (s.val.2 j)) :
    p.Coprime (giantTwoSidedPatternCopiedProduct C s.val.2*giantTwoSidedPatternAuxiliaryProduct a) := by
  have hmem : p∈P j := hp.elim (fun h => markedPhysicalLabelSet_subset _ _ h)
    (fun h => markedPhysicalLabelSet_subset _ _ h)
  exact ((hP j p hmem).coprime_iff_not_dvd).mpr
    (fun hd => hn ((giantTwoSidedPattern_dilation_dvd_iff_of_active hP hdis h j hp).mp hd))

theorem giantTwoSidedPattern_new_labels_card {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) {k ell : ℕ} {C : J → Finset (Fin k)}
    {step : ℤ} (hstep : 0<step.natAbs) (hsize : ∀ j p,p∈P j → step.natAbs<p)
    {Z Z' : Finset ℕ} {s : GiantTwoSidedEndpointState P (k+ell) Z}
    {t : GiantTwoSidedEndpointState P (k+ell) Z'} {a : GiantTwoSidedPatternAuxiliary P C}
    (h : GiantTwoSidedPatternCondition C step s t a) (j : J) :
    (markedPhysicalLabelSet t.val.2 j \ markedPhysicalLabelSet s.val.2 j).card = ell+(C j).card := by
  have hcard := card_sdiff_add_card_inter (markedPhysicalLabelSet t.val.2 j) (markedPhysicalLabelSet s.val.2 j)
  rw [inter_comm,giantTwoSidedPattern_common_labels hP hdis hstep hsize h j,
    giantTwoSidedPatternCopiedValues_card _ _ _ (s.property.1 j),markedPhysicalLabelSet_card _ t.property.1 j] at hcard
  have hC : (C j).card≤k := by simpa only [card_univ,Fintype.card_fin] using card_le_card (subset_univ (C j))
  omega

theorem giantTwoSidedEndpointPermute_labelSet {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    {Z : Finset ℕ} (π : J → Equiv.Perm (Fin M)) (s : GiantTwoSidedEndpointState P M Z) (j : J) :
    markedPhysicalLabelSet (giantTwoSidedEndpointPermute π s).val.2 j = markedPhysicalLabelSet s.val.2 j := by
  ext p
  simp only [markedPhysicalLabelSet,mem_image,mem_univ,true_and]
  change (∃ l,(s.val.2 j (π j l):ℕ) = p) ↔ ∃ l,(s.val.2 j l:ℕ)=p
  constructor
  · rintro ⟨l,hl⟩
    exact ⟨π j l,hl⟩
  · rintro ⟨l,hl⟩
    exact ⟨(π j).symm l,by simpa only [Equiv.apply_symm_apply] using hl⟩

def giantTwoSidedPathPrimeRuns {J : Type*} {P : J → Finset ℕ} {M n : ℕ}
    (a : Fin (n+1) → MarkedPhysicalMarking P M) (j : J) (p : ℕ) : ℕ :=
  (if p∈markedPhysicalLabelSet (a 0) j then 1 else 0) +
    ∑ i : Fin n,if p∈markedPhysicalLabelSet (a i.succ) j \ markedPhysicalLabelSet (a i.castSucc) j
      then 1 else 0

theorem giantTwoSidedPathPrimeRuns_sum {J : Type*} {P : J → Finset ℕ} {M n : ℕ}
    (a : Fin (n+1) → MarkedPhysicalMarking P M) (ha : MarkedPhysicalMarkingDistinct (a 0)) (j : J) :
    (∑ p∈P j,giantTwoSidedPathPrimeRuns a j p) = M +
      ∑ i : Fin n,(markedPhysicalLabelSet (a i.succ) j \ markedPhysicalLabelSet (a i.castSucc) j).card := by
  have hcount (S : Finset ℕ) (hS : S ⊆ P j) : (∑ p∈P j,if p∈S then (1:ℕ) else 0)=S.card := by
    rw [← sum_filter,filter_mem_eq_inter,inter_eq_right.mpr hS]
    simp
  unfold giantTwoSidedPathPrimeRuns
  rw [sum_add_distrib,hcount _ (markedPhysicalLabelSet_subset _ _),markedPhysicalLabelSet_card _ ha j,sum_comm]
  congr 1
  apply sum_congr rfl
  intro i _
  exact hcount _ ((sdiff_subset).trans (markedPhysicalLabelSet_subset _ _))

theorem giantTwoSidedPatternPath_run_charge {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) {k ell n : ℕ}
    {C : Fin n → J → Finset (Fin k)} {Z : Finset ℕ}
    (s : Fin (n+1) → GiantTwoSidedEndpointState P (k+ell) Z)
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    (hstep : ∀ i,0<(step i).natAbs) (hsize : ∀ i j p,p∈P j → (step i).natAbs<p)
    (h : ∀ i,GiantTwoSidedPatternCondition (C i) (step i)
      (giantTwoSidedEndpointPermute (π i) (s i.castSucc))
      (giantTwoSidedEndpointPermute (τ i) (s i.succ)) (aux i)) :
    markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell)*
      (∏ i,giantTwoSidedPatternFreshMass P (C i) ell) =
      ∏ j,∏ p∈P j,(bandReciprocalMass (P j))⁻¹^
        (giantTwoSidedPathPrimeRuns (fun i => (s i).val.2) j p) := by
  have hcount (j : J) : (∑ p∈P j,giantTwoSidedPathPrimeRuns (fun i => (s i).val.2) j p) =
      k+ell+(∑ i : Fin n, (ell+(C i j).card)) := by
    rw [giantTwoSidedPathPrimeRuns_sum _ (s 0).property.1 j]
    congr 1
    apply sum_congr rfl
    intro i _
    simpa only [giantTwoSidedEndpointPermute_labelSet] using
      giantTwoSidedPattern_new_labels_card hP hdis (hstep i) (hsize i) (h i) j
  unfold markedPhysicalMass giantTwoSidedPatternFreshMass
  rw [Finset.prod_comm (s:=(univ : Finset (Fin n))) (t:=(univ : Finset J)),← prod_mul_distrib]
  apply prod_congr rfl
  intro j _
  rw [prod_pow_eq_pow_sum,prod_pow_eq_pow_sum,hcount j,← pow_add]

end
end ArtinMatthews
