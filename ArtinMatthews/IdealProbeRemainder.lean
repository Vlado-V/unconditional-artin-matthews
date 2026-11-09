module

public import ArtinMatthews.IdealProbeComponents


set_option backward.privateInPublic true
@[expose] public section

/-! The sum of all non-full probe components is a contraction. This
keeps the exceptional raw terms grouped before taking absolute values. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealHoeffdingTransform_sub {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ}
    (b : ∀ j,OrthonormalBasis ↥(P j) ℂ (EuclideanSpace ℂ ↥(P j)))
    (f g : MarkedPhysicalMarking P M → ℂ) :
    idealHoeffdingTransform P b (fun a => f a-g a)=fun t =>
      idealHoeffdingTransform P b f t-idealHoeffdingTransform P b g t := by
  have he : idealWeightedVector P (fun a => f a-g a)=idealWeightedVector P f-idealWeightedVector P g := by
    apply WithLp.ofLp_injective
    funext a
    change (Real.sqrt (idealLabelMass P M a):ℂ)*(f a-g a)=
      (Real.sqrt (idealLabelMass P M a):ℂ)*f a-(Real.sqrt (idealLabelMass P M a):ℂ)*g a
    ring
  funext t
  unfold idealHoeffdingTransform
  rw [he,map_sub]
  rfl

def idealProbeRemainder {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (probes tail : Finset (J × Fin M))
    (f : MarkedPhysicalMarking P M → ℂ) : MarkedPhysicalMarking P M → ℂ :=
  fun a => idealAverageSet P tail f a-idealProbeProjection P probes tail f a

theorem idealProbeRemainder_transform {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (hw : ∀ j p,0 < markedHarmonicAtom (P j) p)
    (b : ∀ j,OrthonormalBasis ↥(P j) ℂ (EuclideanSpace ℂ ↥(P j)))
    (a₀ : ∀ j,↥(P j)) (hb : ∀ j,b j (a₀ j)=idealProbabilityRoot (markedHarmonicAtom (P j)))
    (probes tail : Finset (J × Fin M)) (f : MarkedPhysicalMarking P M → ℂ) :
    idealHoeffdingTransform P b (idealProbeRemainder P probes tail f)=fun t =>
      if Disjoint (idealFullSupport a₀ t) tail ∧ ¬probes ⊆ idealFullSupport a₀ t
      then idealHoeffdingTransform P b f t else 0 := by
  unfold idealProbeRemainder
  rw [idealHoeffdingTransform_sub,
    idealHoeffdingTransform_average P hV hw b a₀ hb,
    idealProbeProjection_transform P hV hw b a₀ hb]
  funext t
  simp only [idealAverageSurvives_iff]
  by_cases ht : Disjoint (idealFullSupport a₀ t) tail <;>
    by_cases hp : probes ⊆ idealFullSupport a₀ t <;> simp [ht,hp]

theorem idealProbeRemainder_energy_le {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (hw : ∀ j p,0 < markedHarmonicAtom (P j) p)
    (b : ∀ j,OrthonormalBasis ↥(P j) ℂ (EuclideanSpace ℂ ↥(P j)))
    (a₀ : ∀ j,↥(P j)) (hb : ∀ j,b j (a₀ j)=idealProbabilityRoot (markedHarmonicAtom (P j)))
    (probes tail : Finset (J × Fin M)) (f : MarkedPhysicalMarking P M → ℂ) :
    idealLabelEnergy P M (idealProbeRemainder P probes tail f) ≤ idealLabelEnergy P M f := by
  rw [← idealHoeffdingTransform_energy P hV b,
    idealProbeRemainder_transform P hV hw b a₀ hb,← idealHoeffdingTransform_energy P hV b f]
  apply sum_le_sum
  intro t _
  dsimp only
  split_ifs with h
  · rfl
  · simp

end
end ArtinMatthews
