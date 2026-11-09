module

public import ArtinMatthews.SourceGeneratorPrefix
public import ArtinMatthews.SourceProductPhasePrimitive
public import ArtinMatthews.SourcePrimeExponentProducts
public import ArtinMatthews.ReflectionCoefficientRow


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization SIntegerQuotient
open StandardAdelic QuadraticWeil SourceCRTNormalization
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
local notation "R" => sourceRing F S₀
local notation "T" => sourceHilbertSeed F S₀
local notation "S" => sourceHilbertSet F S₀
local notation "a" => sourcePrimeExponentGenerator F hζ S₀

include hBad in
theorem sourcePoissonExponentPhase_primitive (e : SourcePrimeExponents F S₀) (b : R)
    (hb : b ≠ 0) (hbe : b = a e) :
    (sIntegerQuotientPhase F S b hb).IsPrimitive := by
  let I := e.support
  let P (i : I) := i.val.val
  let A (i : I) := sourceAllowedPrimeGenerator F hζ S₀ i.val
  have hP : Pairwise fun i j => P i ≠ P j := by
    intro i j hij h
    exact hij (Subtype.ext (Subtype.ext h))
  have hS (i : I) : P i ∉ principalizingSet T := i.val.property
  have hA (i : I) :
      (P i).asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing T)) = Ideal.span {A i} :=
    sourceAllowedPrimeGenerator_ideal F hζ S₀ i.val
  have htrace (i : I) : P i ∉ traceBadPlaces F := fun h =>
    hS i (hBad (Finset.mem_union_left _ h))
  have hEq : b = ∏ i : I, A i ^ e i.val :=
    hbe.trans (sourcePrimeExponentGenerator_prefix F hζ S₀ e I le_rfl)
  clear hbe
  subst b
  exact sourceProductQuotientPhase_primitive T P hP hS A hA (fun i => e i.val) htrace

include hBad in
theorem sourcePoissonProductPhase_primitive (s A : SourcePrimeExponents F S₀) :
    (sIntegerQuotientPhase F S (a s * a A)
      (mul_ne_zero (sourcePrimeExponentGenerator_ne_zero F hζ S₀ s)
        (sourcePrimeExponentGenerator_ne_zero F hζ S₀ A))).IsPrimitive :=
  sourcePoissonExponentPhase_primitive F S₀ hζ hBad (s + A) _
    (mul_ne_zero (sourcePrimeExponentGenerator_ne_zero F hζ S₀ s)
      (sourcePrimeExponentGenerator_ne_zero F hζ S₀ A))
    (sourcePrimeExponentGenerator_add F hζ S₀ s A).symm

end
end ArtinMatthews.SourceEulerAssembly
