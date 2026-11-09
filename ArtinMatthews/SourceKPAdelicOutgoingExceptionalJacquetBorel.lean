module

public import ArtinMatthews.SourceKPJacquetFlatDiagonal
public import ArtinMatthews.SourceKPAdelicOutgoingLocalReceiver


set_option backward.privateInPublic true
@[expose] public section

/-! The actual exceptional all-rest Borel carrier has the negative
cube action used by the diagonal Jacquet estimates. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K)) (hs : 0 < (1 / 6 : ℂ).re)

local notation "W" => sourceKPAdelicOutgoingRegularizedRetainedCarrier K hζ
  (Singleton.singleton P : Finset (HeightOneSpectrum (𝓞 K))) (1 / 6 : ℂ) hs
local notation "ρ₀" => sourceKPAdelicOutgoingRegularizedLocalBorelRepresentation K hζ P (1 / 6 : ℂ) hs

local instance sourceKPOutgoingExceptionalJacquetBorelAddCommGroup : AddCommGroup W := Submodule.addCommGroup _

theorem sourceKPAdelicOutgoingExceptionalJacquet_negativeCubeLaw : SourceKPJacquetNegativeCubeLaw K hζ P (V := W) ρ₀ :=
  sourceKPAdelicOutgoingExceptionalLocalBorelRepresentation_cube K hζ P hs

end
end ArtinMatthews
