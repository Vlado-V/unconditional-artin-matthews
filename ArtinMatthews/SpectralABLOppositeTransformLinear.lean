module

public import ArtinMatthews.SpectralABLOppositeKTransform


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Complex
open scoped BigOperators
noncomputable section

theorem spectralABLOppositeTransform_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ) (z : ℂ)
    (hI : ∀ i ∈ s, Integrable (spectralKLCompactOrderIntegrand (f i) (2*I*z))) :
    spectralABLOppositeTransform (fun x => ∑ i ∈ s, f i x) z =
      ∑ i ∈ s, spectralABLOppositeTransform (f i) z := by
  have he : spectralKLCompactOrderIntegrand (fun x => ∑ i ∈ s, f i x) (2*I*z) =
      fun x => ∑ i ∈ s, spectralKLCompactOrderIntegrand (f i) (2*I*z) x := by
    funext x
    simp only [spectralKLCompactOrderIntegrand,spectralKLPhysicalCompactDiv,div_eq_mul_inv,
      Finset.sum_mul,Finset.mul_sum]
  simp only [spectralABLOppositeTransform,spectralABLOppositeFourierWeight,spectralKLCompactOrderTransform,he]
  rw [integral_finsetSum s hI,Finset.mul_sum,Finset.mul_sum]

end
end ArtinMatthews
