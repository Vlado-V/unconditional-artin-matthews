module

public import ArtinMatthews.SourcePoissonInitialContour
public import Mathlib.MeasureTheory.Integral.DominatedConvergence


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open MeasureTheory
noncomputable section

/-- A summable height-independent coefficient majorant justifies moving a series
through an absolutely integrable vertical kernel. -/
theorem sourcePoisson_integral_mul_tsum
    {α ι : Type} [MeasurableSpace α] [Countable ι] {μ : Measure α}
    (K : α → ℂ) (hK : Integrable K μ) (A : ι → α → ℂ)
    (hA : ∀ i, Measurable (A i)) (B : ι → ℝ) (hB : Summable B)
    (hbound : ∀ i p, ‖A i p‖ ≤ B i) :
    (∫ p, K p * (∑' i, A i p) ∂μ) = ∑' i, ∫ p, K p * A i p ∂μ := by
  apply (hasSum_integral_of_dominated_convergence (fun i p => ‖K p‖ * B i) ?_ ?_ ?_ ?_ ?_).tsum_eq.symm
  · exact fun i => hK.aestronglyMeasurable.mul (hA i).aestronglyMeasurable
  · intro i
    filter_upwards with p
    exact norm_mul (K p) (A i p) ▸ mul_le_mul_of_nonneg_left (hbound i p) (norm_nonneg _)
  · filter_upwards with p
    exact hB.mul_left _
  · simpa only [tsum_mul_left] using hK.norm.mul_const (∑' i, B i)
  · filter_upwards with p
    have h : Summable (fun i => A i p) := by
      exact (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => hbound i p) hB).of_norm
    exact h.hasSum.mul_left _

end
end ArtinMatthews.SourcePhysical

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain MeasureTheory AllowedGenerators
open VaryingKummerAnalytic QuadraticWeil SourcePhysical
open scoped NumberField Classical ContDiff
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)

def sourcePoissonFrequencyKernel (X Y Z : ℝ) (W M : ℝ → ℂ)
    (u : {u : sourceRing F S₀ // u ≠ 0}) : SourcePoissonHeights → ℂ :=
  sourcePoissonTripleKernel X Y Z 4 4 2 W M
    (fun p => (sourcePoissonFrequencyNorm F S₀ u : ℂ) ^ (-sourcePoissonVertical 2 p.1.2))

omit [IsTotallyComplex F] in
theorem sourcePoissonFrequencyKernel_integrable {X Y Z : ℝ}
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (W M : ℝ → ℂ) (hW : Integrable W) (hM : Integrable M)
    (hWm : Measurable W) (hMm : Measurable M)
    (u : {u : sourceRing F S₀ // u ≠ 0}) :
    Integrable (sourcePoissonFrequencyKernel F S₀ X Y Z W M u) sourcePoissonHeightMeasure := by
  have hq := sourcePoissonFrequencyNorm_pos F S₀ u
  apply sourcePoissonTripleKernel_integrable hX hY hZ _ _ _ W M _ hW hM hWm hMm
    (B := sourcePoissonFrequencyNorm F S₀ u ^ (-(2 : ℝ)))
  · apply Continuous.measurable
    simp_rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hq.ne')]
    unfold sourcePoissonVertical
    fun_prop
  · intro p
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hq, Complex.neg_re, sourcePoissonVertical_re]

/-- In each actual nonzero frequency row, all four exterior ideal sums commute
with the three initial source contour integrals. -/
theorem sourcePoissonInitialRow_integral_eq_tsum {X Y Z : ℝ}
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (W M : ℝ → ℂ) (hW : Integrable W) (hM : Integrable M)
    (hWm : Measurable W) (hMm : Measurable M)
    (u : {u : sourceRing F S₀ // u ≠ 0}) :
    let K := sourcePoissonFrequencyKernel F S₀ X Y Z W M u
    (∫ p : SourcePoissonHeights, K p *
      sourceGlobalCalF F hζ S₀ hS η u.val
        (sourcePoissonVertical 4 p.2) (sourcePoissonVertical 4 p.1.1)
        (sourcePoissonVertical 2 p.1.2) ∂sourcePoissonHeightMeasure) =
    ∑' a : SourceExponentCoordinates F S₀, ∫ p : SourcePoissonHeights, K p *
      sourceGlobalEulerTerm F hζ S₀ hS η u.val
        (sourcePoissonVertical 4 p.2) (sourcePoissonVertical 4 p.1.1)
        (sourcePoissonVertical 2 p.1.2) a ∂sourcePoissonHeightMeasure := by
  let : Countable (Ideal (𝓞 F)) := by
    apply Set.countable_univ_iff.mp
    apply (Set.countable_iUnion (fun n : ℕ =>
      (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) n).countable)).mono
    intro I _
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨Ideal.absNorm I, le_rfl⟩
  let : Countable (HeightOneSpectrum (𝓞 F)) := HeightOneSpectrum.asIdeal_injective.countable
  dsimp [sourceGlobalCalF]
  apply sourcePoisson_integral_mul_tsum
    (B := sourceCoordinateMajorant F S₀ 3 10 3 12)
  · exact sourcePoissonFrequencyKernel_integrable F S₀ hX hY hZ W M hW hM hWm hMm u
  · exact fun a => (sourceGlobalEulerTerm_initial_continuous F S₀ hζ hS η u.val a).measurable
  · exact sourceCoordinateMajorant_summable F S₀ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · intro a p
    have h := sourceGlobalEulerTerm_norm_le F S₀ hζ hS η u.val
      (sourcePoissonVertical 4 p.2) (sourcePoissonVertical 4 p.1.1)
      (sourcePoissonVertical 2 p.1.2) a
    norm_num only [sourcePoissonVertical_re] at h
    exact h

end
end ArtinMatthews.SourceEulerAssembly
