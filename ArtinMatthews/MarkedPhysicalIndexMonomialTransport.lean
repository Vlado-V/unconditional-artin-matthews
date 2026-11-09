module

public import ArtinMatthews.MarkedPhysicalIndexDampingFormula
public import ArtinMatthews.MarkedPhysicalIndexResidueRoot


set_option backward.privateInPublic true
@[expose] public section

/-! The original lifted-index monomial is the exact selected-residue
scalar on the normalized good set. No arithmetic or validity test is
discarded in passing to the finite root-count input. -/

noncomputable section
namespace ArtinMatthews
attribute [local instance] Classical.propDecidable

theorem markedPhysicalIndexRootValid_selected_iff
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ}
    (hP : ∀ j p,p∈P j → p.Prime) {M n R : ℕ}
    (i : MarkedPhysicalCoordinateIndex P M n R) (hR : 1≤R)
    (T : Finset ℕ) (hT : T⊆markedPhysicalBandPrimes P) {U V : ℝ} (hU : 1<U) (hV : 1<V)
    (r : MarkedPhysicalCanonicalRoot (markedPhysicalBonferroniModulus Finset.univ i.1 T) U (16*U) V (2*V)) :
    MarkedPhysicalIndexRootValid i r ↔
      markedPhysicalResidueLabelValid (markedPhysicalBonferroniModulus_squarefree hP Finset.univ i.1 hT)
        r.1 Finset.univ i.1 (markedPhysicalCoordinateIndexPath i.2.1)
        (markedPhysicalCoordinateIndexPath_primitive hR i.2.1) := by
  let : NeZero (markedPhysicalBonferroniModulus Finset.univ i.1 T) :=
    ⟨(markedPhysicalBonferroniModulus_pos hP Finset.univ i.1 hT).ne'⟩
  have hh := markedPhysicalLiftedLabelValid_iff_selected_residue hP Finset.univ i.1
    (markedPhysicalCoordinateIndexPath i.2.1) (markedPhysicalCoordinateIndexPath_primitive hR i.2.1)
    T hT (markedPhysicalCanonicalRootPosition r) (markedPhysicalCanonicalCompletion r)
    (markedPhysicalCanonicalCompletion_det hU hV r) r.1 (markedPhysicalCanonicalCompletion_reduction hU hV r)
  simpa only [MarkedPhysicalIndexRootValid,markedPhysicalIndexLiftedPosition,Finset.mem_univ,forall_const] using hh

theorem markedPhysicalIndexMonomial_selected_eq
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ}
    (hP : ∀ j p,p∈P j → p.Prime) {M n R : ℕ}
    (i : MarkedPhysicalCoordinateIndex P M n R) (hR : 1≤R)
    (q : ℝ) (T : Finset ℕ) (hT : T⊆markedPhysicalBandPrimes P) {U V : ℝ} (hU : 1<U) (hV : 1<V)
    (r : MarkedPhysicalCanonicalRoot (markedPhysicalBonferroniModulus Finset.univ i.1 T) U (16*U) V (2*V)) :
    markedPhysicalJointBonferroniMonomial Finset.univ i.1 (markedMemoryVisitQ q n)
        (fun v => (markedPhysicalIndexLiftedPosition i r v).1.natAbs) T =
      markedPhysicalResidueBonferroniMonomial (markedPhysicalBonferroniModulus_squarefree hP Finset.univ i.1 hT)
        r.1 Finset.univ i.1 (markedMemoryVisitQ q n) (markedPhysicalCoordinateIndexPath i.2.1)
        (markedPhysicalCoordinateIndexPath_primitive hR i.2.1) T := by
  let : NeZero (markedPhysicalBonferroniModulus Finset.univ i.1 T) :=
    ⟨(markedPhysicalBonferroniModulus_pos hP Finset.univ i.1 hT).ne'⟩
  exact markedPhysicalBonferroniMonomial_eq_selected_residue hP Finset.univ i.1 (markedMemoryVisitQ q n)
    (markedPhysicalCoordinateIndexPath i.2.1) (markedPhysicalCoordinateIndexPath_primitive hR i.2.1)
    T hT (markedPhysicalCanonicalRootPosition r) (markedPhysicalCanonicalCompletion r)
    (markedPhysicalCanonicalCompletion_det hU hV r) r.1 (markedPhysicalCanonicalCompletion_reduction hU hV r)

def markedPhysicalIndexMonomialWeight {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x d₀ Y U V : ℝ) {n R S : ℕ}
    (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) n R)
    (hR : 1≤R) (q : ℝ) (T : Finset ℕ)
    (r : MarkedPhysicalCanonicalRoot S U (16*U) V (2*V)) : ℂ :=
  if MarkedPhysicalIndexRootValid i r ∧
      markedPhysicalCoordinateIndexPath i.2.1 (Fin.last n)=(1,0) ∧
      markedRootNormalizedPoint U V r.2.1∈markedPhysicalCoordinateIndexGoodSet e x d₀ Y U V i hR then
    (markedPhysicalJointBonferroniMonomial Finset.univ i.1 (markedMemoryVisitQ q n)
      (fun v => (markedPhysicalIndexLiftedPosition i r v).1.natAbs) T:ℂ)
  else 0

theorem markedPhysicalIndexMonomialWeight_selected
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (x d₀ Y U V : ℝ)
    {n R : ℕ}
    (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) n R)
    (hR : 1≤R) (hU : 1<U) (hV : 1<V) (q : ℝ) (T : Finset ℕ)
    (hT : T⊆markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x))
    (r : MarkedPhysicalCanonicalRoot (markedPhysicalBonferroniModulus Finset.univ i.1 T) U (16*U) V (2*V)) :
    markedPhysicalIndexMonomialWeight e x d₀ Y U V i hR q T r =
      if markedPhysicalCoordinateIndexPath i.2.1 (Fin.last n)=(1,0) then
        if markedRootNormalizedPoint U V r.2.1∈markedPhysicalCoordinateIndexGoodSet e x d₀ Y U V i hR then
          (markedPhysicalCoordinateIndexResidueFactor (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
            i hR q T hT r.1:ℂ) else 0
      else 0 := by
  have hv := markedPhysicalIndexRootValid_selected_iff
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) i hR T hT hU hV r
  have hm := markedPhysicalIndexMonomial_selected_eq
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) i hR q T hT hU hV r
  unfold markedPhysicalIndexMonomialWeight markedPhysicalCoordinateIndexResidueFactor
  rw [hm]
  simp only [hv]
  split_ifs <;> simp_all

end ArtinMatthews
