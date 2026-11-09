module

public import ArtinMatthews.SourceWeilSquareImage


set_option backward.privateInPublic true
@[expose] public section

/-! The actual analytic Weil character on the one chosen paper B6. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain
open QuadraticWeil AllowedGenerators
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)

def sourceChosenWeilCharacter : chosenB K hζ S₀ →* ℂˣ :=
  (sLocalAnalyticWeilCharacter K (sourceHilbertSet K S₀) hS
    (chosenB_squareImage K hζ S₀) (chosenB_squareImage_isotropic_all K hζ S₀)).comp
      (chosenB_squareImageHom K hζ S₀)

theorem sourceChosenWeilCharacter_apply (b : chosenB K hζ S₀) :
    (sourceChosenWeilCharacter K hζ S₀ hS b : ℂ) =
      sLocalAnalyticWeil K (sourceHilbertSet K S₀)
        (sourceRingSquareMap K (sourceHilbertSet K S₀) b.val) := rfl

theorem sourceChosenWeilCharacter_sq (b : chosenB K hζ S₀) :
    sourceChosenWeilCharacter K hζ S₀ hS b ^ 2 = 1 :=
  sLocalAnalyticWeilCharacter_sq K (sourceHilbertSet K S₀) hS
    (chosenB_squareImage K hζ S₀) (chosenB_squareImage_isotropic_all K hζ S₀)
    (chosenB_squareImageHom K hζ S₀ b)

theorem sourceChosenWeilCharacter_source_value (b : chosenB K hζ S₀) :
    (sLocalAnalyticWeil K (sourceHilbertSet K S₀)
      ((sourceRingSquareMap K (sourceHilbertSet K S₀) b.val)⁻¹))⁻¹ =
      (sourceChosenWeilCharacter K hζ S₀ hS b : ℂ) :=
  sLocalAnalyticWeilCharacter_source_value K (sourceHilbertSet K S₀) hS
    (chosenB_squareImage K hζ S₀) (chosenB_squareImage_isotropic_all K hζ S₀)
    (chosenB_squareImageHom K hζ S₀ b)

end
end ArtinMatthews
