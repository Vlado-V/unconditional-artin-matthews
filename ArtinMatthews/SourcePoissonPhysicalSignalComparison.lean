module

public import ArtinMatthews.SourcePoissonOriginalInitialContour
public import ArtinMatthews.SourcePoissonOrbitPrincipalSplit
public import ArtinMatthews.SourcePrincipalPoissonRow
public import ArtinMatthews.SourceNonprincipalRowSeries
public import ArtinMatthews.SourceProbeComparison


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SourcePhysical MeasureTheory Filter Asymptotics
open VaryingKummerAnalytic QuadraticWeil
open scoped NumberField Classical Topology
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)
variable (v : InfinitePlace F)
local notation "S" => sourceHilbertSet F S₀

def sourcePoissonPhysicalProbeAtScales
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀) (Z : ℝ) : ℂ :=
  sourcePoissonOriginalIntegral F S₀ hζ η v hBad (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z

def sourcePoissonNonprincipalAtScales (hJ : J ≠ ⊥) (Z : ℝ) : ℂ :=
  sourcePoissonNonprincipalRowSeries F S₀ hζ η hJ v (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z

/-- The literal physical probe, the actual residue signal and the three
actual remainders are joined with all identities discharged. -/
theorem sourcePoissonPhysicalProbeAtScales_eq_signal_remainders
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    (hJ : J ≠ ⊥) (hcut : principalAngularCutoff F J ⊆ sourceHilbertSet F S₀)
    {Z : ℝ} (hZ : 0 < Z) :
    sourcePoissonPhysicalProbeAtScales F S₀ hζ η v hBad Z =
      sourcePrincipalPoissonDoubleConstant F hζ S₀ v * principalAngularGaussianSignal hζ η S Z +
        sourcePrincipalPoissonWRemainder F hζ S₀ η v Z +
        sourcePrincipalPoissonZRemainder F hζ S₀ η v Z +
        sourcePoissonNonprincipalAtScales F S₀ hζ η v hJ Z := by
  let X : ℝ := Z ^ (9 / 10 : ℝ)
  let Y : ℝ := Z ^ (133 / 1000 : ℝ)
  have hX : 0 < X := Real.rpow_pos_of_pos hZ _
  have hY : 0 < Y := Real.rpow_pos_of_pos hZ _
  have hI := (sourcePoissonOriginalIntegral_eq_actualOrbitSeries F S₀ hζ η v hBad hX hY hZ).2
  have hSplit := sourcePoissonActualOrbitSeries_split_principal F S₀ hζ η v hBad hX hY hZ
  have hPrincipal := sourcePrincipalPoissonOrbitRow_eq_signal_add_remainders F hζ S₀ η v
    hBad hJ hcut hZ
  have hOther :
      (∑' u : SourceNonprincipalFrequencyIndex F S₀,
        sourcePoissonOrbitContribution F S₀ hζ η v hBad X Y Z u.val) =
      sourcePoissonNonprincipalAtScales F S₀ hζ η v hJ Z := by
    unfold sourcePoissonNonprincipalAtScales sourcePoissonNonprincipalRowSeries
    apply tsum_congr
    intro u
    exact (sourceContinuedPoissonRowIntegral_eq_orbitRow F S₀ hζ η hJ hBad
      (probePrimeCutoff_subset_principalAngularCutoff.trans hcut) v
      (sourceFrequencyRepresentative F hζ S₀ u.val) hX hY hZ).symm
  exact hI.trans (hSplit.trans (congrArg₂ (fun x y : ℂ => x + y) hPrincipal hOther))

/-- Exact comparison for the real physical probe. The inputs are precisely
the physical second-moment bound and the total nonprincipal contour bound. -/
theorem sourcePoissonAngularSignal_bound_of_physical_and_nonprincipal
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    (hJ : J ≠ ⊥) (hcut : principalAngularCutoff F J ⊆ sourceHilbertSet F S₀)
    (hPhysical : sourcePoissonPhysicalProbeAtScales F S₀ hζ η v hBad =O[atTop]
      (fun Z : ℝ => Z ^ (933 / 2000 + 1 / 100000 : ℝ)))
    (hOther : sourcePoissonNonprincipalAtScales F S₀ hζ η v hJ =O[atTop]
      (fun Z : ℝ => Z ^ (7 / 15 - 1 / 2500 : ℝ))) :
    principalAngularGaussianSignal hζ η S =O[atTop]
      (fun Z : ℝ => Z ^ (7 / 15 - 1 / 20000 : ℝ)) := by
  apply principalAngularGaussianSignal_bound_of_three_remainders hζ η S
    (sourcePoissonPhysicalProbeAtScales F S₀ hζ η v hBad)
    (sourcePrincipalPoissonWRemainder F hζ S₀ η v)
    (sourcePrincipalPoissonZRemainder F hζ S₀ η v)
    (sourcePoissonNonprincipalAtScales F S₀ hζ η v hJ)
    (sourcePrincipalPoissonDoubleConstant F hζ S₀ v)
    (sourcePrincipalPoissonDoubleConstant_ne_zero F hζ S₀ v)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with Z hZ
    exact sourcePoissonPhysicalProbeAtScales_eq_signal_remainders F S₀ hζ η v hBad hJ hcut hZ
  · exact hPhysical
  · exact sourcePrincipalPoissonWRemainder_bigO F hζ S₀ η v hJ hcut
  · exact sourcePrincipalPoissonZRemainder_bigO F hζ S₀ η v hJ hcut
  · exact hOther

end
end ArtinMatthews.SourceEulerAssembly
