module

public import ArtinMatthews.SourcePrincipalContourAssembly
public import ArtinMatthews.SourcePrincipalInitialIntegralShift


set_option backward.privateInPublic true
@[expose] public section

/-! The selected original Poisson orbit row is the true principal signal plus its two remainders. -/

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain MeasureTheory AllowedGenerators
open VaryingKummerAnalytic QuadraticWeil SourcePhysical
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)
variable (v : InfinitePlace F)
local notation "S" => sourceHilbertSet F S₀
local notation "u₁" => sourceFrequencyRepresentative F hζ S₀ (sourceFrequencyPrincipalIndex F S₀)

theorem sourcePrincipalPoissonOrbitRow_eq_initialIntegral
    (hS : standardWeilBadPlaces F ⊆ S) (hcut : probePrimeCutoff F ⊆ S)
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    (∑' a : SourceExponentCoordinates F S₀,
      sourcePoissonOrbitTerm F S₀ hζ hS η v sourceProbeW1Complex X Y Z u₁ a) =
    sourcePrincipalPoissonIntegral F hζ S₀ η v X Y Z 4 4 2 := by
  rw [sourcePoissonOrbitRow_eq_initialContour F S₀ hζ hS η v sourceProbeW1Complex
    sourceProbeW1Complex_compact sourceProbeW1Complex_positive_support sourceProbeW1Complex_contDiff hX hY hZ u₁,
    sourcePrincipalPoissonIntegral]
  apply congrArg (fun w : ℂ => sourcePoissonNormalization ^ 3 * w)
  apply integral_congr_ae
  filter_upwards with p
  have h := (sourcePrincipalPoissonKernel_initial F hζ S₀ η v hS hcut X Y Z p).symm
  simpa only [sourcePrincipalPoissonKernelOnLines, sourcePoissonFrequencyKernel, sourcePoissonTripleKernel,
    sourcePoissonOneRow, sourceProbeW1Mellin, mul_assoc] using h

theorem sourcePrincipalPoissonOrbitRow_eq_signal_add_remainders
    (hS : standardWeilBadPlaces F ⊆ S) (hJ : J ≠ ⊥) (hcut : principalAngularCutoff F J ⊆ S)
    {Z : ℝ} (hZ : 0 < Z) :
    (∑' a : SourceExponentCoordinates F S₀, sourcePoissonOrbitTerm F S₀ hζ hS η v sourceProbeW1Complex
      (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z u₁ a) =
    sourcePrincipalPoissonDoubleConstant F hζ S₀ v * principalAngularGaussianSignal hζ η S Z +
      sourcePrincipalPoissonWRemainder F hζ S₀ η v Z +
      sourcePrincipalPoissonZRemainder F hζ S₀ η v Z := by
  have hX : 0 < Z ^ (9 / 10 : ℝ) := Real.rpow_pos_of_pos hZ _
  have hY : 0 < Z ^ (133 / 1000 : ℝ) := Real.rpow_pos_of_pos hZ _
  rw [sourcePrincipalPoissonOrbitRow_eq_initialIntegral F hζ S₀ η v hS
    (probePrimeCutoff_subset_principalAngularCutoff.trans hcut) hX hY hZ,
    sourcePrincipalPoissonIntegral_initial_shift F hζ S₀ η v hJ hcut hX hY hZ]
  exact sourcePrincipalPoissonIntegral_crossings F hζ S₀ η v hJ hcut hZ

end
end ArtinMatthews.SourceEulerAssembly
