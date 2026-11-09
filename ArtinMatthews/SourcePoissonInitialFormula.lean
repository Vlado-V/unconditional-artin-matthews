module

public import ArtinMatthews.SourcePoissonOrbitRows


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open MeasureTheory
noncomputable section

theorem sourcePoissonHeight_integral_iterated (f : SourcePoissonHeights → ℂ)
    (hf : Integrable f sourcePoissonHeightMeasure) :
    (∫ p, f p ∂sourcePoissonHeightMeasure) = ∫ u : ℝ, ∫ w : ℝ, ∫ z : ℝ, f ((w, z), u) := by
  unfold sourcePoissonHeightMeasure at hf ⊢
  rw [integral_prod_symm f hf]
  apply integral_congr_ae
  filter_upwards [hf.prod_left_ae] with u hu
  exact integral_prod (fun p : ℝ × ℝ => f (p, u)) hu

end
end ArtinMatthews.SourcePhysical

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

local notation "Ŵ" => fun W y => mellin W (sourcePoissonVertical 4 y)
local notation "M̂" => fun y => sourceSLocalProbeMellin F hζ (sourceHilbertSet F S₀) v (sourcePoissonVertical 2 y)

/-- The literal finite union of exterior frequency rows equals the original
three initial contours in the order `ξ,w,z`. -/
theorem sourcePoissonOrbitSeries_eq_initialContours
    (W₁ : ℝ → ℂ) (hcompact : HasCompactSupport W₁)
    (hpositive : tsupport W₁ ⊆ Set.Ioi 0) (hsmooth : ContDiff ℝ ∞ W₁)
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (U : Finset {u : sourceRing F S₀ // u ≠ 0}) :
    (∑ u ∈ U, ∑' a : SourceExponentCoordinates F S₀,
      sourcePoissonOrbitTerm F S₀ hζ hS η v W₁ X Y Z u a) =
    sourcePoissonNormalization ^ 3 * ∫ tξ : ℝ, ∫ tw : ℝ, ∫ tz : ℝ,
      sourcePoissonTripleKernel X Y Z 4 4 2 (Ŵ W₁) M̂
        (sourcePoissonInitialRows F S₀ hζ hS η U) ((tw, tz), tξ) := by
  have hInt := sourcePoissonInitialContour_integrable F S₀ hζ hS η v hX hY hZ
    W₁ hcompact hpositive hsmooth U
  rw [← sourcePoissonHeight_integral_iterated _ hInt]
  simp_rw [sourcePoissonOrbitRow_eq_initialContour F S₀ hζ hS η v W₁ hcompact hpositive
    hsmooth hX hY hZ]
  rw [← Finset.mul_sum]
  have hSingle (u : {u : sourceRing F S₀ // u ≠ 0}) :=
    sourcePoissonInitialContour_integrable F S₀ hζ hS η v hX hY hZ
      W₁ hcompact hpositive hsmooth {u}
  have hIntegrable (u : {u : sourceRing F S₀ // u ≠ 0}) (_ : u ∈ U) :
      Integrable (fun p => sourcePoissonFrequencyKernel F S₀ X Y Z (Ŵ W₁) M̂ u p *
        sourceGlobalCalF F hζ S₀ hS η u.val (sourcePoissonVertical 4 p.2)
          (sourcePoissonVertical 4 p.1.1) (sourcePoissonVertical 2 p.1.2))
        sourcePoissonHeightMeasure := by
    have h := hSingle u
    change Integrable (fun p => sourcePoissonTripleKernel X Y Z 4 4 2 (Ŵ W₁) M̂
      (sourcePoissonInitialRows F S₀ hζ hS η {u}) p) sourcePoissonHeightMeasure at h
    simpa only [sourcePoissonFrequencyKernel, sourcePoissonTripleKernel, sourcePoissonInitialRows,
      Finset.sum_singleton, mul_assoc] using h
  rw [← integral_finsetSum U hIntegrable]
  congr 1
  apply integral_congr_ae
  filter_upwards with p
  simp only [sourcePoissonFrequencyKernel, sourcePoissonTripleKernel, sourcePoissonInitialRows,
    mul_assoc, Finset.mul_sum]

end
end ArtinMatthews.SourceEulerAssembly
