module

public import ArtinMatthews.SourcePoissonPhysicalSignalComparison
public import ArtinMatthews.SourceNonprincipalProbeRemainder


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SourcePhysical Filter Asymptotics
open VaryingKummerAnalytic QuadraticWeil
open scoped NumberField Classical Topology
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)
variable (v : InfinitePlace F)

/-- The actual contour estimates reduce the source06 angular power bound
to the one physical upper bound for the original probe. -/
theorem sourcePoissonAngularSignal_bound_of_physical
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    (hJ : J ≠ ⊥) (hcut : principalAngularCutoff F J ⊆ sourceHilbertSet F S₀)
    (hPhysical : sourcePoissonPhysicalProbeAtScales F S₀ hζ η v hBad =O[atTop]
      (fun Z : ℝ => Z ^ (933 / 2000 + 1 / 100000 : ℝ))) :
    principalAngularGaussianSignal hζ η (sourceHilbertSet F S₀) =O[atTop]
      (fun Z : ℝ => Z ^ (7 / 15 - 1 / 20000 : ℝ)) :=
  sourcePoissonAngularSignal_bound_of_physical_and_nonprincipal F S₀ hζ η v hBad hJ hcut hPhysical
    (sourcePoissonNonprincipalRowSeries_source06_bound F S₀ hζ η hJ hBad hcut v)

end
end ArtinMatthews.SourceEulerAssembly
