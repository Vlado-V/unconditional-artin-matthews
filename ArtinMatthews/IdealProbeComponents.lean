module

public import ArtinMatthews.IdealSymmetricProbe


set_option backward.privateInPublic true
@[expose] public section

/-! The complete source probe decomposition retains every subset
component. Its sum is exactly the tail-averaged original vector. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def idealProbeComponent {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (probes S tail : Finset (J × Fin M))
    (f : MarkedPhysicalMarking P M → ℂ) : MarkedPhysicalMarking P M → ℂ :=
  idealProbeProjection P S (tail ∪ (probes \ S)) f

theorem idealProbeComponent_full {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (probes tail : Finset (J × Fin M))
    (f : MarkedPhysicalMarking P M → ℂ) :
    idealProbeComponent P probes probes tail f=idealProbeProjection P probes tail f := by
  simp [idealProbeComponent]

theorem idealProbeComponent_support {ι : Type*} [DecidableEq ι]
    (probes S tail U : Finset ι) (hS : S ⊆ probes) :
    S ⊆ U ∧ Disjoint U (tail ∪ (probes \ S)) ↔ U ∩ probes=S ∧ Disjoint U tail := by
  constructor
  · rintro ⟨hSU,hdis⟩
    refine ⟨?_,(disjoint_union_right.mp hdis).1⟩
    apply Subset.antisymm
    · intro i hi
      by_contra hn
      exact disjoint_left.mp (disjoint_union_right.mp hdis).2
        (mem_inter.mp hi).1 (mem_sdiff.mpr ⟨(mem_inter.mp hi).2,hn⟩)
    · exact fun i hi => mem_inter.mpr ⟨hSU hi,hS hi⟩
  · rintro ⟨he,hdis⟩
    refine ⟨?_,disjoint_union_right.mpr ⟨hdis,?_⟩⟩
    · intro i hi
      have := mem_inter.mp (show i∈U ∩ probes from he.symm ▸ hi)
      exact this.1
    · apply disjoint_left.mpr
      intro i hi hpi
      exact (mem_sdiff.mp hpi).2 (he ▸ mem_inter.mpr ⟨hi,(mem_sdiff.mp hpi).1⟩)

theorem idealHoeffdingTransform_injective {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (hw : ∀ j p,0 < markedHarmonicAtom (P j) p)
    (b : ∀ j,OrthonormalBasis ↥(P j) ℂ (EuclideanSpace ℂ ↥(P j))) :
    Function.Injective (idealHoeffdingTransform (M:=M) P b) := by
  intro f g h
  funext a
  rw [← idealProductMode_expansion P hV hw b f a,h,idealProductMode_expansion P hV hw b g a]

theorem idealHoeffdingTransform_sum {J I : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ}
    (b : ∀ j,OrthonormalBasis ↥(P j) ℂ (EuclideanSpace ℂ ↥(P j)))
    (s : Finset I) (f : I → MarkedPhysicalMarking P M → ℂ) :
    idealHoeffdingTransform P b (fun a => ∑ i∈s,f i a)=fun t => ∑ i∈s,idealHoeffdingTransform P b (f i) t := by
  have he : idealWeightedVector P (fun a => ∑ i∈s,f i a)=∑ i∈s,idealWeightedVector P (f i) := by
    apply WithLp.ofLp_injective
    funext a
    simp only [idealWeightedVector,WithLp.ofLp_toLp,WithLp.ofLp_sum,Finset.sum_apply,mul_sum]
  funext t
  unfold idealHoeffdingTransform
  rw [he,map_sum]
  simp only [WithLp.ofLp_sum,Finset.sum_apply]

theorem idealProbeComponent_transform {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (hw : ∀ j p,0 < markedHarmonicAtom (P j) p)
    (b : ∀ j,OrthonormalBasis ↥(P j) ℂ (EuclideanSpace ℂ ↥(P j)))
    (a₀ : ∀ j,↥(P j)) (hb : ∀ j,b j (a₀ j)=idealProbabilityRoot (markedHarmonicAtom (P j)))
    (probes S tail : Finset (J × Fin M)) (hS : S ⊆ probes)
    (f : MarkedPhysicalMarking P M → ℂ) :
    idealHoeffdingTransform P b (idealProbeComponent P probes S tail f)=fun t =>
      if idealFullSupport a₀ t ∩ probes=S ∧ Disjoint (idealFullSupport a₀ t) tail
      then idealHoeffdingTransform P b f t else 0 := by
  rw [idealProbeComponent,idealProbeProjection_transform P hV hw b a₀ hb]
  funext t
  simp only [idealProbeComponent_support probes S tail _ hS]

theorem idealProbeComponents_sum {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (hw : ∀ j p,0 < markedHarmonicAtom (P j) p)
    (b : ∀ j,OrthonormalBasis ↥(P j) ℂ (EuclideanSpace ℂ ↥(P j)))
    (a₀ : ∀ j,↥(P j)) (hb : ∀ j,b j (a₀ j)=idealProbabilityRoot (markedHarmonicAtom (P j)))
    (probes tail : Finset (J × Fin M)) (f : MarkedPhysicalMarking P M → ℂ) :
    (fun a => ∑ S∈probes.powerset,idealProbeComponent P probes S tail f a)=idealAverageSet P tail f := by
  apply idealHoeffdingTransform_injective P hV hw b
  rw [idealHoeffdingTransform_sum,idealHoeffdingTransform_average P hV hw b a₀ hb]
  funext t
  simp only [idealAverageSurvives_iff]
  have hterm (S : Finset (J × Fin M)) (hS : S∈probes.powerset) :
      idealHoeffdingTransform P b (idealProbeComponent P probes S tail f) t=
        if idealFullSupport a₀ t ∩ probes=S ∧ Disjoint (idealFullSupport a₀ t) tail
        then idealHoeffdingTransform P b f t else 0 :=
    congrFun (idealProbeComponent_transform P hV hw b a₀ hb probes S tail (mem_powerset.mp hS) f) t
  rw [sum_congr rfl hterm]
  rw [sum_eq_single (idealFullSupport a₀ t ∩ probes)]
  · simp
  · intro S _ hS
    rw [ite_eq_right (fun h => hS h.1.symm)]
  · intro h
    exact (h (mem_powerset.mpr inter_subset_right)).elim

end
end ArtinMatthews
