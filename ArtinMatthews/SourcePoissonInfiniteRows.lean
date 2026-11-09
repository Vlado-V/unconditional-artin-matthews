module

public import ArtinMatthews.SourcePoissonOrbitAbsolute
public import ArtinMatthews.SourcePoissonInitialFormula


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain MeasureTheory AllowedGenerators
open VaryingKummerAnalytic QuadraticWeil SourcePhysical
open scoped NumberField Classical ContDiff BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)
variable (v : InfinitePlace F)

local notation "qu" => sourcePoissonFrequencyNorm F S₀
local notation "Ŵ" => fun W y => mellin W (sourcePoissonVertical 4 y)
local notation "M̂" => fun y => sourceSLocalProbeMellin F hζ (sourceHilbertSet F S₀) v (sourcePoissonVertical 2 y)

def sourcePoissonOneRow (u : {u : sourceRing F S₀ // u ≠ 0}) (p : SourcePoissonHeights) : ℂ :=
  (qu u : ℂ) ^ (-sourcePoissonVertical 2 p.1.2) *
    sourceGlobalCalF F hζ S₀ hS η u.val (sourcePoissonVertical 4 p.2)
      (sourcePoissonVertical 4 p.1.1) (sourcePoissonVertical 2 p.1.2)

theorem sourcePoissonOneRow_measurable (u : {u : sourceRing F S₀ // u ≠ 0}) :
    Measurable (sourcePoissonOneRow F S₀ hζ hS η u) := by
  have h (p : SourcePoissonHeights) :
      sourcePoissonInitialRows F S₀ hζ hS η {u} p = sourcePoissonOneRow F S₀ hζ hS η u p := by
    simp only [sourcePoissonInitialRows, Finset.sum_singleton, sourcePoissonOneRow]
  exact (funext h) ▸ sourcePoissonInitialRows_measurable F S₀ hζ hS η {u}

theorem sourcePoissonOneRow_norm_le (u : {u : sourceRing F S₀ // u ≠ 0}) (p : SourcePoissonHeights) :
    ‖sourcePoissonOneRow F S₀ hζ hS η u p‖ ≤ (qu u) ^ (-(2 : ℝ)) *
      ∑' a : SourceExponentCoordinates F S₀, sourceCoordinateMajorant F S₀ 3 10 3 12 a := by
  simpa only [sourcePoissonOneRow, sourcePoissonInitialRows, sourcePoissonInitialRowBound,
    Finset.sum_singleton] using sourcePoissonInitialRows_norm_le F S₀ hζ hS η {u} p

/-- Absolute convergence and the exact initial Mellin identity for a countable
family of original frequency rows with summable inverse-squared norms. -/
theorem sourcePoissonOrbitSeries_countable_initialContours
    (W₁ : ℝ → ℂ) (hcompact : HasCompactSupport W₁)
    (hpositive : tsupport W₁ ⊆ Set.Ioi 0) (hsmooth : ContDiff ℝ ∞ W₁)
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    {ι : Type} [Countable ι] (U : ι → {u : sourceRing F S₀ // u ≠ 0})
    (hU : Summable fun i => (qu (U i)) ^ (-(2 : ℝ))) :
    let G := sourcePoissonTripleKernel X Y Z 4 4 2 (Ŵ W₁) M̂
      (fun p => ∑' i, sourcePoissonOneRow F S₀ hζ hS η (U i) p)
    Integrable G sourcePoissonHeightMeasure ∧
      Summable (fun i => ‖∑' a : SourceExponentCoordinates F S₀,
        sourcePoissonOrbitTerm F S₀ hζ hS η v W₁ X Y Z (U i) a‖) ∧
      (∑' i, ∑' a : SourceExponentCoordinates F S₀,
        sourcePoissonOrbitTerm F S₀ hζ hS η v W₁ X Y Z (U i) a) =
      sourcePoissonNormalization ^ 3 * ∫ tξ : ℝ, ∫ tw : ℝ, ∫ tz : ℝ, G ((tw, tz), tξ) := by
  let K := sourcePoissonTripleKernel X Y Z 4 4 2 (Ŵ W₁) M̂ (fun _ => 1)
  let A (i : ι) := sourcePoissonOneRow F S₀ hζ hS η (U i)
  let B (i : ι) := (qu (U i)) ^ (-(2 : ℝ)) *
    ∑' a : SourceExponentCoordinates F S₀, sourceCoordinateMajorant F S₀ 3 10 3 12 a
  have hK : Integrable K sourcePoissonHeightMeasure := by
    apply sourcePoissonTripleKernel_integrable hX hY hZ (B := 1)
    · exact smoothMellin_verticalIntegrable W₁ hcompact hpositive hsmooth 4
    · exact sourceSLocalProbeMellin_verticalIntegrable F hζ (sourceHilbertSet F S₀) v 2 (by norm_num)
    · exact ((smoothMellin_entire W₁ hcompact hpositive hsmooth.continuous).continuous.comp
        (sourcePoissonVertical_continuous 4)).measurable
    · exact (sourceSLocalProbeMellin_continuous_vertical F S₀ hζ v (by norm_num)).measurable
    · exact measurable_const
    · intro p
      simp
  have hA (i : ι) : Measurable (A i) := sourcePoissonOneRow_measurable F S₀ hζ hS η (U i)
  have hB : Summable B := hU.mul_right _
  have hbound (i : ι) (p : SourcePoissonHeights) : ‖A i p‖ ≤ B i :=
    sourcePoissonOneRow_norm_le F S₀ hζ hS η (U i) p
  have ⟨hG, hNorm⟩ := sourcePoisson_mul_tsum_integrable_and_summable K hK A hA B hB hbound
  have hSeries := sourcePoisson_integral_mul_tsum K hK A hA B hB hbound
  have hRow (i : ι) :
      (∑' a : SourceExponentCoordinates F S₀,
        sourcePoissonOrbitTerm F S₀ hζ hS η v W₁ X Y Z (U i) a) =
      sourcePoissonNormalization ^ 3 * (∫ p, K p * A i p ∂sourcePoissonHeightMeasure) := by
    simpa only [K, A, sourcePoissonOneRow, sourcePoissonFrequencyKernel,
      sourcePoissonTripleKernel, mul_one, mul_assoc] using
      sourcePoissonOrbitRow_eq_initialContour F S₀ hζ hS η v W₁ hcompact hpositive
        hsmooth hX hY hZ (U i)
  have hEq : (fun p => K p * (∑' i, A i p)) =
      sourcePoissonTripleKernel X Y Z 4 4 2 (Ŵ W₁) M̂ (fun p => ∑' i, A i p) := by
    funext p
    simp only [K, sourcePoissonTripleKernel, mul_one]
  have hG' := hEq ▸ hG
  dsimp only
  refine ⟨hG', ?_, ?_⟩
  · simp_rw [hRow]
    exact sourcePoisson_summable_norm_scaled_integral (fun i p => K p * A i p)
      hNorm (sourcePoissonNormalization ^ 3)
  · rw [← sourcePoissonHeight_integral_iterated _ hG']
    simp_rw [hRow]
    rw [tsum_mul_left, ← hSeries]
    simp only [K, A, sourcePoissonTripleKernel, mul_one]

end
end ArtinMatthews.SourceEulerAssembly
