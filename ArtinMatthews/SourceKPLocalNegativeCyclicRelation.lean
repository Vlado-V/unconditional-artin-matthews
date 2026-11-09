module

public import ArtinMatthews.SourceKPFiniteCyclicFiber


set_option backward.privateInPublic true
@[expose] public section

/-! The zero relation in the whole negative cyclic representation, with
its literal translation vectors and complex coefficients. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic SourcePhysical QuadraticWeil
open scoped NumberField AdeleRing Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "G₀" => SourceFiniteKP2Projective K hζ P.val
local notation "C₋" => sourceKPTameSphericalCyclicSpace K hζ S₀ P
local notation "r₋" => sourceKPTameSphericalCyclicRepresentation K hζ S₀ P
local notation "v₋" => sourceKPTameCyclicSphericalVector K hζ S₀ P

def SourceKPLocalNegativeCyclicRelation {I : Type*} [Fintype I] (g : I → G₀) (c : I → ℂ) : Prop :=
  (∑ i, c i • r₋ (g i) v₋ : C₋) = 0

theorem sourceKPLocalNegativeCyclicRelation_iff {I : Type*} [Fintype I] (g : I → G₀) (c : I → ℂ) :
    SourceKPLocalNegativeCyclicRelation K hζ S₀ P g c ↔ (∑ i, c i • r₋ (g i) v₋ : C₋) = 0 :=
  Iff.rfl

end
end ArtinMatthews
