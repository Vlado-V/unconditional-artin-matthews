module

public import ArtinMatthews.IdealHoeffdingProjection
public import ArtinMatthews.IdealCoefficientTensor
public import ArtinMatthews.IdealProbeMask


set_option backward.privateInPublic true
@[expose] public section

/-! The source's actual alternating probe projection satisfies the
full-product symmetric survivor estimate. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
attribute [local instance] Classical.propDecidable

def idealFullSupport {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {M : ℕ} (a₀ : ∀ j,↥(P j))
    (t : MarkedPhysicalMarking P M) : Finset (J × Fin M) :=
  univ.filter (fun v => t v.1 v.2≠a₀ v.1)

theorem idealCoefficientSupport_membership {α : Type*} {M : ℕ}
    (a₀ : α) (t : Fin M → α) (i : Fin M) :
    i∈idealCoefficientSupport a₀ t ↔ t i≠a₀ := by
  unfold idealCoefficientSupport
  rw [mem_filter]
  exact and_iff_right (mem_univ i)

theorem idealFullSupport_mem {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {M : ℕ} (a₀ : ∀ j,↥(P j))
    (t : MarkedPhysicalMarking P M) (j : J) (i : Fin M) :
    (j,i)∈idealFullSupport a₀ t ↔ i∈idealCoefficientSupport (a₀ j) (t j) := by
  rw [idealCoefficientSupport_membership]
  unfold idealFullSupport
  rw [mem_filter]
  exact and_iff_right (mem_univ (j,i))

theorem idealAverageSurvives_iff {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {M : ℕ} (a₀ : ∀ j,↥(P j))
    (S : Finset (J × Fin M)) (t : MarkedPhysicalMarking P M) :
    IdealAverageSurvives a₀ S t ↔ Disjoint (idealFullSupport a₀ t) S := by
  constructor
  · intro h
    apply disjoint_left.mpr
    rintro ⟨j,i⟩ hs hS
    exact (mem_filter.mp hs).2 (h j i hS)
  · intro h j i hS
    by_contra hn
    exact disjoint_left.mp h (mem_filter.mpr ⟨mem_univ _,hn⟩) hS

theorem idealProbeProjection_modeSum {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (hw : ∀ j p,0 < markedHarmonicAtom (P j) p)
    (b : ∀ j,OrthonormalBasis ↥(P j) ℂ (EuclideanSpace ℂ ↥(P j)))
    (a₀ : ∀ j,↥(P j)) (hb : ∀ j,b j (a₀ j)=idealProbabilityRoot (markedHarmonicAtom (P j)))
    (probes tail : Finset (J × Fin M)) (f : MarkedPhysicalMarking P M → ℂ)
    (a : MarkedPhysicalMarking P M) :
    idealProbeProjection P probes tail f a=
      ∑ t,(if probes ⊆ idealFullSupport a₀ t ∧ Disjoint (idealFullSupport a₀ t) tail
        then idealHoeffdingTransform P b f t else 0)*idealProductMode b t a := by
  unfold idealProbeProjection
  simp_rw [idealAverageSet_modeSum P hV hw b a₀ hb,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro t _
  simp_rw [idealAverageSurvives_iff]
  calc
    _ = (∑ S∈probes.powerset,(-1:ℂ)^S.card*
        (if Disjoint (idealFullSupport a₀ t) (tail ∪ S) then idealHoeffdingTransform P b f t else 0))*
        idealProductMode b t a := by
      rw [sum_mul]
      apply sum_congr rfl
      intro S _
      ring
    _ = _ := by rw [idealProbe_alternating_mask]

theorem idealProbeProjection_transform {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (hw : ∀ j p,0 < markedHarmonicAtom (P j) p)
    (b : ∀ j,OrthonormalBasis ↥(P j) ℂ (EuclideanSpace ℂ ↥(P j)))
    (a₀ : ∀ j,↥(P j)) (hb : ∀ j,b j (a₀ j)=idealProbabilityRoot (markedHarmonicAtom (P j)))
    (probes tail : Finset (J × Fin M)) (f : MarkedPhysicalMarking P M → ℂ) :
    idealHoeffdingTransform P b (idealProbeProjection P probes tail f)=fun t =>
      if probes ⊆ idealFullSupport a₀ t ∧ Disjoint (idealFullSupport a₀ t) tail
      then idealHoeffdingTransform P b f t else 0 := by
  rw [show idealProbeProjection P probes tail f=fun a => ∑ t,
      (if probes ⊆ idealFullSupport a₀ t ∧ Disjoint (idealFullSupport a₀ t) tail
      then idealHoeffdingTransform P b f t else 0)*idealProductMode b t a
      from funext (idealProbeProjection_modeSum P hV hw b a₀ hb probes tail f)]
  exact idealHoeffdingTransform_modeSum P hV hw b _

theorem idealProbeProjection_energy {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (hw : ∀ j p,0 < markedHarmonicAtom (P j) p)
    (b : ∀ j,OrthonormalBasis ↥(P j) ℂ (EuclideanSpace ℂ ↥(P j)))
    (a₀ : ∀ j,↥(P j)) (hb : ∀ j,b j (a₀ j)=idealProbabilityRoot (markedHarmonicAtom (P j)))
    (probes tail : Finset (J × Fin M)) (f : MarkedPhysicalMarking P M → ℂ) :
    idealLabelEnergy P M (idealProbeProjection P probes tail f)=
      ∑ t,if probes ⊆ idealFullSupport a₀ t ∧ Disjoint (idealFullSupport a₀ t) tail
        then ‖idealHoeffdingTransform P b f t‖^2 else 0 := by
  rw [← idealHoeffdingTransform_energy P hV b,
    idealProbeProjection_transform P hV hw b a₀ hb]
  apply sum_congr rfl
  intro t _
  split_ifs with h <;> simp [h]

theorem idealProbeProjection_symmetric_bound {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (hw : ∀ j p,0 < markedHarmonicAtom (P j) p)
    (b : ∀ j,OrthonormalBasis ↥(P j) ℂ (EuclideanSpace ℂ ↥(P j)))
    (a₀ : ∀ j,↥(P j)) (hb : ∀ j,b j (a₀ j)=idealProbabilityRoot (markedHarmonicAtom (P j)))
    (probes tail : Finset (J × Fin M)) (groupProbes groupTail : J → Finset (Fin M)) (G : Finset J)
    (hp : ∀ j∈G,∀ i∈groupProbes j,(j,i)∈probes)
    (ht : ∀ j∈G,∀ i∈groupTail j,(j,i)∈tail)
    (hPT : ∀ j∈G,Disjoint (groupProbes j) (groupTail j)) (hM : 0 < M)
    (hm : ∀ j∈G,1 ≤ (groupProbes j).card) (hell : ∀ j∈G,1 ≤ (groupTail j).card)
    (hlarge : ∀ j∈G,((groupProbes j).card+(groupTail j).card)*
      ((groupProbes j).card+(groupTail j).card-1) ≤ M)
    (f : MarkedPhysicalMarking P M → ℂ) (hf : IdealSymmetric f) :
    idealLabelEnergy P M (idealProbeProjection P probes tail f) ≤
      (∏ j∈G,((2:ℝ)/((groupProbes j).card+1 : ℕ)))*idealLabelEnergy P M f := by
  rw [idealProbeProjection_energy P hV hw b a₀ hb]
  have himp (t : MarkedPhysicalMarking P M)
      (h : probes ⊆ idealFullSupport a₀ t ∧ Disjoint (idealFullSupport a₀ t) tail) :
      IdealCoefficientBlockEvent a₀ groupProbes groupTail G t := by
    intro j hj
    constructor
    · intro i hi
      exact (idealFullSupport_mem a₀ t j i).mp (h.1 (hp j hj i hi))
    · apply disjoint_left.mpr
      intro i hi hti
      exact disjoint_left.mp h.2 ((idealFullSupport_mem a₀ t j i).mpr hi) (ht j hj i hti)
  calc
    _ ≤ ∑ t,if IdealCoefficientBlockEvent a₀ groupProbes groupTail G t
        then ‖idealHoeffdingTransform P b f t‖^2 else 0 := by
      apply sum_le_sum
      intro t _
      split_ifs with h h'
      · rfl
      · exact (h' (himp t h)).elim
      · positivity
      · rfl
    _ ≤ _ := by
      rw [← idealHoeffdingTransform_energy P hV b f]
      exact idealCoefficientTensor_bound a₀ (idealHoeffdingTransform P b f)
        (idealHoeffdingTransform_symmetric P b f hf) groupProbes groupTail G hPT hM hm hell hlarge

end
end ArtinMatthews
