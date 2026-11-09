module

public import ArtinMatthews.SourcePoissonActualInitialContour
public import ArtinMatthews.SourceNonprincipalFrequencyDyads


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SourcePhysical MeasureTheory
open VaryingKummerAnalytic QuadraticWeil
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)
variable (v : InfinitePlace F)
local notation "S" => sourceHilbertSet F S₀
local notation "U" => sourceFrequencyRepresentative F hζ S₀
local notation "P" => sourceFrequencyPrincipalIndex F S₀
local notation "E" => SourceExponentCoordinates F S₀

/-- The exact contribution of one original orbit representative before
continuation of its associated Hecke row. -/
def sourcePoissonOrbitContribution
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    (X Y Z : ℝ) (u : SourceFrequencyRepresentativeIndex F S₀) : ℂ :=
  ∑' a : E, sourcePoissonOrbitTerm F S₀ hζ hBad η v sourceProbeW1Complex X Y Z (U u) a

/-- Split off precisely the chosen principal row from the full infinite
frequency sum. Absolute convergence holds for the original orbit values. -/
theorem sourcePoissonActualOrbitSeries_split_principal
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    sourcePoissonActualOrbitSeries F S₀ hζ hBad η v X Y Z =
      sourcePoissonOrbitContribution F S₀ hζ η v hBad X Y Z P +
        ∑' u : SourceNonprincipalFrequencyIndex F S₀,
          sourcePoissonOrbitContribution F S₀ hζ η v hBad X Y Z u.val := by
  let C := sourcePoissonOrbitContribution F S₀ hζ η v hBad X Y Z
  have hSumNorm : Summable (fun u => ‖C u‖) :=
    (sourcePoissonActualOrbitSeries_eq_initialContour F S₀ hζ hBad η v hX hY hZ).2.1
  have hSum : Summable C := hSumNorm.of_norm
  let B : Finset (SourceFrequencyRepresentativeIndex F S₀) := {P}
  let K : Set (SourceFrequencyRepresentativeIndex F S₀) := (B : Set _)ᶜ
  let e : SourceNonprincipalFrequencyIndex F S₀ ≃ K :=
    Equiv.subtypeEquivRight (fun u => by simp [K, B])
  have hSplit := hSum.sum_add_tsum_compl (s := B)
  have hCompl : (∑' u : K, C u.val) = ∑' u : SourceNonprincipalFrequencyIndex F S₀, C u.val :=
    (e.tsum_eq (fun u : K => C u.val)).symm
  have hEq :
      (∑' u, C u) = C P + ∑' u : SourceNonprincipalFrequencyIndex F S₀, C u.val := by
    calc
      _ = C P + ∑' u : K, C u.val := by
        simpa only [B, Finset.sum_singleton] using hSplit.symm
      _ = _ := congrArg (fun z : ℂ => C P + z) hCompl
  exact hEq

end
end ArtinMatthews.SourceEulerAssembly
