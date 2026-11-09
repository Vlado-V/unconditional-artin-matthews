module

public import ArtinMatthews.SourceFiniteDensityProduct
public import OAI.NumberTheory.DirichletL.CubicSieve.ArithmeticBins


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceHyperbolicGreen
open OAI.CubicEisenstein MeasureTheory
open scoped BigOperators ENNReal Topology
noncomputable section

abbrev ProductSpace (ι : Type*) := ι → EuclideanSpatial

def productUpper (ι : Type*) : Set (ProductSpace ι) :=
  Set.univ.pi (fun _ => euclideanUpperHalf)

def productDensity {ι : Type*} [Fintype ι] (p : ProductSpace ι) : ℝ≥0∞ :=
  ∏ i, hyperbolicDensity (p i)

def productVolume (ι : Type*) [Fintype ι] : Measure (ProductSpace ι) :=
  Measure.pi (fun _ => hyperbolicEuclideanVolume)

instance sourceHyperbolic_sigmaFinite : SigmaFinite hyperbolicEuclideanVolume := by
  unfold hyperbolicEuclideanVolume hyperbolicDensity
  infer_instance

theorem productUpper_isOpen (ι : Type*) [Fintype ι] : IsOpen (productUpper ι) := by
  have h : productUpper ι = ⋂ i : ι, {p : ProductSpace ι | 0 < p i 2} := by
    ext p
    simp [productUpper, euclideanUpperHalf]
  rw [h]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt continuous_const (by fun_prop)

theorem productDensity_measurable (ι : Type*) [Fintype ι] :
    Measurable (productDensity (ι := ι)) := by
  unfold productDensity
  apply Finset.measurable_prod
  intro i _
  exact hyperbolicDensity_measurable.comp (measurable_pi_apply i)

theorem productVolume_eq_density (ι : Type*) [Fintype ι] :
    productVolume ι = (volume.restrict (productUpper ι)).withDensity (productDensity (ι := ι)) := by
  have h := @finite_pi_withDensity ι EuclideanSpatial _ _
    (fun _ : ι => volume.restrict euclideanUpperHalf) (fun _ => inferInstance)
    (fun _ : ι => hyperbolicDensity) (fun _ => hyperbolicDensity_measurable)
    (fun _ => sourceHyperbolic_sigmaFinite)
  rw [← Measure.restrict_pi_pi] at h
  exact h

end
end ArtinMatthews.SourceHyperbolicGreen
