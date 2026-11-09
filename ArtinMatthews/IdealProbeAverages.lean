module

public import ArtinMatthews.IdealProbeComponents
public import ArtinMatthews.IdealAveragePairing


set_option backward.privateInPublic true
@[expose] public section

/-! Source probe components are exactly independent of missing probes
and mean zero when an indicated probe is averaged. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealAverageSet_mix {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (S : Finset (G × Fin M))
    (f : MarkedPhysicalMarking P M → ℂ) (a b : MarkedPhysicalMarking P M) :
    idealAverageSet P S f (idealMix S a b)=idealAverageSet P S f a := by
  unfold idealAverageSet idealLabelExpectation
  apply sum_congr rfl
  intro z _
  have he : idealMix S (idealMix S a b) z=idealMix S a z := by
    funext g i
    simp only [idealMix]
    split_ifs <;> rfl
  dsimp only
  rw [he]

theorem idealHoeffdingTransform_zero {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ}
    (b : ∀ g,OrthonormalBasis ↥(P g) ℂ (EuclideanSpace ℂ ↥(P g))) :
    idealHoeffdingTransform (M:=M) P b 0=0 := by
  have he : idealWeightedVector (M:=M) P 0=0 := by
    apply WithLp.ofLp_injective
    funext a
    simp [idealWeightedVector]
  funext t
  simp only [idealHoeffdingTransform,he,map_zero,PiLp.zero_apply,Pi.zero_apply]

theorem idealAverageSet_probeProjection {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (hV : ∀ g,0 < bandReciprocalMass (P g))
    (hw : ∀ g p,0 < markedHarmonicAtom (P g) p)
    (b : ∀ g,OrthonormalBasis ↥(P g) ℂ (EuclideanSpace ℂ ↥(P g)))
    (a₀ : ∀ g,↥(P g)) (hb : ∀ g,b g (a₀ g)=idealProbabilityRoot (markedHarmonicAtom (P g)))
    (A S tail : Finset (G × Fin M)) (f : MarkedPhysicalMarking P M → ℂ) :
    idealAverageSet P A (idealProbeProjection P S tail f)=idealProbeProjection P S (tail ∪ A) f := by
  apply idealHoeffdingTransform_injective P hV hw b
  rw [idealHoeffdingTransform_average P hV hw b a₀ hb,
    idealProbeProjection_transform P hV hw b a₀ hb,
    idealProbeProjection_transform P hV hw b a₀ hb]
  funext t
  dsimp only
  simp only [idealAverageSurvives_iff,disjoint_union_right]
  by_cases hS : S ⊆ idealFullSupport a₀ t <;>
    by_cases ht : Disjoint (idealFullSupport a₀ t) tail <;>
    by_cases hA : Disjoint (idealFullSupport a₀ t) A <;> simp [hS,ht,hA]

theorem idealAverageSet_probeProjection_fixed {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (hV : ∀ g,0 < bandReciprocalMass (P g))
    (hw : ∀ g p,0 < markedHarmonicAtom (P g) p)
    (b : ∀ g,OrthonormalBasis ↥(P g) ℂ (EuclideanSpace ℂ ↥(P g)))
    (a₀ : ∀ g,↥(P g)) (hb : ∀ g,b g (a₀ g)=idealProbabilityRoot (markedHarmonicAtom (P g)))
    (A S tail : Finset (G × Fin M)) (hA : A ⊆ tail)
    (f : MarkedPhysicalMarking P M → ℂ) :
    idealAverageSet P A (idealProbeProjection P S tail f)=idealProbeProjection P S tail f := by
  rw [idealAverageSet_probeProjection P hV hw b a₀ hb,union_eq_left.mpr hA]

theorem idealAverageSet_probeProjection_zero {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (hV : ∀ g,0 < bandReciprocalMass (P g))
    (hw : ∀ g p,0 < markedHarmonicAtom (P g) p)
    (b : ∀ g,OrthonormalBasis ↥(P g) ℂ (EuclideanSpace ℂ ↥(P g)))
    (a₀ : ∀ g,↥(P g)) (hb : ∀ g,b g (a₀ g)=idealProbabilityRoot (markedHarmonicAtom (P g)))
    (A S tail : Finset (G × Fin M)) (hAS : (A ∩ S).Nonempty)
    (f : MarkedPhysicalMarking P M → ℂ) :
    idealAverageSet P A (idealProbeProjection P S tail f)=0 := by
  rw [idealAverageSet_probeProjection P hV hw b a₀ hb]
  apply idealHoeffdingTransform_injective P hV hw b
  rw [idealProbeProjection_transform P hV hw b a₀ hb,idealHoeffdingTransform_zero]
  funext t
  obtain ⟨v,hv⟩ := hAS
  have hno : ¬(S ⊆ idealFullSupport a₀ t ∧ Disjoint (idealFullSupport a₀ t) (tail ∪ A)) := by
    rintro ⟨hS,hdis⟩
    exact disjoint_left.mp hdis (hS (mem_inter.mp hv).2) (mem_union_right tail (mem_inter.mp hv).1)
  simp only [hno,ite_false,Pi.zero_apply]

theorem idealProbeComponent_independent {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (hV : ∀ g,0 < bandReciprocalMass (P g))
    (hw : ∀ g p,0 < markedHarmonicAtom (P g) p)
    (b : ∀ g,OrthonormalBasis ↥(P g) ℂ (EuclideanSpace ℂ ↥(P g)))
    (a₀ : ∀ g,↥(P g)) (hb : ∀ g,b g (a₀ g)=idealProbabilityRoot (markedHarmonicAtom (P g)))
    (A probes S tail : Finset (G × Fin M)) (hA : A ⊆ tail ∪ (probes \ S))
    (f : MarkedPhysicalMarking P M → ℂ) (x y : MarkedPhysicalMarking P M) :
    idealProbeComponent P probes S tail f (idealMix A x y)=idealProbeComponent P probes S tail f x := by
  have he := idealAverageSet_probeProjection_fixed P hV hw b a₀ hb A S (tail ∪ (probes \ S)) hA f
  change idealAverageSet P A (idealProbeComponent P probes S tail f)=idealProbeComponent P probes S tail f at he
  rw [← congrFun he (idealMix A x y),idealAverageSet_mix,he]

end
end ArtinMatthews
