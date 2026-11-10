module

public import ArtinMatthews.SourceHyperbolicLocalCalculus
public import OAI.NumberTheory.DirichletL.MeanSquare.UnitRows
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceHyperbolicGreen
open OAI.CubicEisenstein MeasureTheory Filter
open scoped Topology ContDiff BigOperators
noncomputable section

def weightedDivergence (f : EuclideanSpatial → ℂ) (p : EuclideanSpatial) : ℂ :=
  -∑ j : Fin 3, coordinatePartial (weightedPartial f j) j p

theorem weightedDivergence_eq_laplacian {f : EuclideanSpatial → ℂ} {p : EuclideanSpatial}
    (hf : ContDiffAt ℝ 2 f p) (hp : 0 < p 2) :
    weightedDivergence f p = positiveEuclideanLaplacian f p / (p 2 : ℂ)^3 := by
  have hpartial (j : Fin 3) : coordinatePartial f j =
      fun q => fderiv ℝ f q (euclideanCoordinateVector j) := rfl
  have hd (j : Fin 3) := weightedPartial_derivative hf hp j j
  simp only [weightedDivergence, Fin.sum_univ_three]
  rw [hd 0, hd 1, hd 2]
  simp only [positiveEuclideanLaplacian, coordinatePartial, Fin.sum_univ_three]
  simp_rw [hpartial]
  norm_num [euclideanCoordinateVector]
  field_simp [Complex.ofReal_ne_zero.mpr hp.ne']
  ring

theorem local_green_direction {f φ : EuclideanSpatial → ℂ}
    (hf : ∀ p ∈ euclideanUpperHalf, ContDiffAt ℝ 2 f p)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ euclideanUpperHalf) (j : Fin 3) :
    (∫ p, star (coordinatePartial φ j p) * weightedPartial f j p) =
      -(∫ p, star (φ p) * coordinatePartial (weightedPartial f j) j p) := by
  have h₁ : Integrable (fun p => star (coordinatePartial φ j p) * weightedPartial f j p) volume := by
    apply compact_star_mul_integrable (test_partial_continuous hφ j) (test_partial_compact hc j)
    intro p hp
    have hh := hsupp (test_partial_support j hp)
    exact (weightedPartial_contDiffAt (hf p hh) hh j).continuousAt
  have h₂ : Integrable (fun p => star (φ p) * coordinatePartial (weightedPartial f j) j p) volume := by
    apply compact_star_mul_integrable hφ.continuous hc
    intro p hp
    have hh := hsupp hp
    exact weightedPartial_derivative_continuousAt (hf p hh) hh j j
  have h₃ : Integrable (fun p => star (φ p) * weightedPartial f j p) volume := by
    apply compact_star_mul_integrable hφ.continuous hc
    intro p hp
    have hh := hsupp hp
    exact (weightedPartial_contDiffAt (hf p hh) hh j).continuousAt
  have h := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (μ := volume) (B := complexHermitianBilin) (f := φ) (g := weightedPartial f j)
    (v := euclideanCoordinateVector j) h₁ h₂ h₃
    (fun p _ => hφ.contDiffAt.differentiableAt (by norm_num))
    (fun p hp => (weightedPartial_contDiffAt (hf p (hsupp hp)) (hsupp hp) j).differentiableAt (by norm_num))
  change (∫ p, star (φ p) * coordinatePartial (weightedPartial f j) j p) =
    -(∫ p, star (coordinatePartial φ j p) * weightedPartial f j p) at h
  calc
    _ = -(-(∫ p, star (coordinatePartial φ j p) * weightedPartial f j p)) := (neg_neg _).symm
    _ = _ := congrArg Neg.neg h.symm

def pairDensity (φ f : EuclideanSpatial → ℂ) (p : EuclideanSpatial) : ℂ :=
  ∑ j : Fin 3, star (coordinatePartial φ j p) * coordinatePartial f j p / (p 2 : ℂ)

theorem pairDensity_integrable {f φ : EuclideanSpatial → ℂ}
    (hf : ∀ p ∈ euclideanUpperHalf, ContDiffAt ℝ 2 f p)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ euclideanUpperHalf) : Integrable (pairDensity φ f) volume := by
  apply integrable_finsetSum
  intro j _
  have h : Integrable (fun p => star (coordinatePartial φ j p) * weightedPartial f j p) volume := by
    apply compact_star_mul_integrable (test_partial_continuous hφ j) (test_partial_compact hc j)
    intro p hp
    have hh := hsupp (test_partial_support j hp)
    exact (weightedPartial_contDiffAt (hf p hh) hh j).continuousAt
  simpa only [weightedPartial, mul_div_assoc] using h

theorem local_green {f φ : EuclideanSpatial → ℂ}
    (hf : ∀ p ∈ euclideanUpperHalf, ContDiffAt ℝ 2 f p)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ euclideanUpperHalf) :
    (∫ p, pairDensity φ f p) =
      ∫ p, star (φ p) * positiveEuclideanLaplacian f p / (p 2 : ℂ)^3 := by
  have hI (j : Fin 3) : Integrable (fun p => star (coordinatePartial φ j p) * weightedPartial f j p) volume := by
    apply compact_star_mul_integrable (test_partial_continuous hφ j) (test_partial_compact hc j)
    intro p hp
    have hh := hsupp (test_partial_support j hp)
    exact (weightedPartial_contDiffAt (hf p hh) hh j).continuousAt
  have hJ (j : Fin 3) : Integrable (fun p => star (φ p) * coordinatePartial (weightedPartial f j) j p) volume := by
    apply compact_star_mul_integrable hφ.continuous hc
    intro p hp
    have hh := hsupp hp
    exact weightedPartial_derivative_continuousAt (hf p hh) hh j j
  have he : (fun p => -(∑ j : Fin 3, star (φ p) * coordinatePartial (weightedPartial f j) j p)) =
      fun p => star (φ p) * positiveEuclideanLaplacian f p / (p 2 : ℂ)^3 := by
    funext p
    by_cases hp : p ∈ tsupport φ
    · rw [mul_div_assoc, ← weightedDivergence_eq_laplacian (hf p (hsupp hp)) (hsupp hp)]
      simp only [weightedDivergence, mul_neg, Finset.mul_sum]
    · have hz : φ p=0 := image_eq_zero_of_notMem_tsupport hp
      simp only [hz, star_zero, zero_mul, Finset.sum_const_zero, neg_zero, zero_div]
  calc
    _ = ∑ j : Fin 3, ∫ p, star (coordinatePartial φ j p) * weightedPartial f j p := by
      rw [← integral_finsetSum _ (fun j _ => hI j)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun p => by simp only [pairDensity, weightedPartial, mul_div_assoc])
    _ = -(∑ j : Fin 3, ∫ p, star (φ p) * coordinatePartial (weightedPartial f j) j p) := by
      simp only [local_green_direction hf hφ hc hsupp, Finset.sum_neg_distrib]
    _ = ∫ p, -(∑ j : Fin 3, star (φ p) * coordinatePartial (weightedPartial f j) j p) := by
      rw [integral_neg, integral_finsetSum _ (fun j _ => hJ j)]
    _ = _ := by rw [he]

theorem tested_laplacian_integrable {f φ : EuclideanSpatial → ℂ}
    (hf : ∀ p ∈ euclideanUpperHalf, ContDiffAt ℝ 2 f p)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ euclideanUpperHalf) :
    Integrable (fun p => star (φ p) * positiveEuclideanLaplacian f p / (p 2 : ℂ)^3) volume := by
  have hJ (j : Fin 3) : Integrable (fun p => star (φ p) * coordinatePartial (weightedPartial f j) j p) volume := by
    apply compact_star_mul_integrable hφ.continuous hc
    intro p hp
    have hh := hsupp hp
    exact weightedPartial_derivative_continuousAt (hf p hh) hh j j
  apply ((integrable_finsetSum Finset.univ (fun j _ => hJ j)).neg).congr
  exact Filter.Eventually.of_forall fun p => by
    change -(∑ j : Fin 3, star (φ p) * coordinatePartial (weightedPartial f j) j p) =
      star (φ p) * positiveEuclideanLaplacian f p / (p 2 : ℂ)^3
    by_cases hp : p ∈ tsupport φ
    · rw [mul_div_assoc, ← weightedDivergence_eq_laplacian (hf p (hsupp hp)) (hsupp hp)]
      simp only [weightedDivergence, mul_neg, Finset.mul_sum]
    · have hz : φ p=0 := image_eq_zero_of_notMem_tsupport hp
      simp only [hz, star_zero, zero_mul, Finset.sum_const_zero, neg_zero, zero_div]

end
end ArtinMatthews.SourceHyperbolicGreen
