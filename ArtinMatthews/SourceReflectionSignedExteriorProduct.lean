module

public import ArtinMatthews.SourceReflectionSignedExteriorLocal
public import ArtinMatthews.SixthExteriorReductionClasses


set_option backward.privateInPublic true
@[expose] public section

/-! The actual exterior product has finite multiplicative support for
an arbitrary field frequency, including frequencies with poles. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic StandardAdelic QuadraticWeil
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K]
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)

local notation "Pr" => SourceExteriorPrime K S₀
local notation "E" => SourcePrimeExponents K S₀
local notation "F" => sourceReflectionSignedExteriorLocal K S₀ hζ hS

theorem sourceReflectionSignedExteriorLocal_eq_one_of_outside (row : E) (active : Finset Pr) (a : Kˣ)
    (P : Pr) (hP : P ∉ active) (hrow : P ∉ row.support) (ha : exteriorPrincipalValuation P.val a = 0) :
    F P row active a = 1 := by
  rw [sourceReflectionSignedExteriorLocal_inactive K S₀ hζ hS P row active a hP,
    ite_eq_right hrow, sourceReflectionTameExteriorWhittaker_eq_one_of_order_zero K S₀ hζ hS P a ha,
    mul_one]

def sourceReflectionSignedExteriorProduct (row : E) (active : Finset Pr) (a : Kˣ) : ℂ :=
  ∏ᶠ P : Pr, F P row active a

local notation "Πext" => sourceReflectionSignedExteriorProduct K S₀ hζ hS

theorem sourceReflectionSignedExteriorProduct_hasFiniteMulSupport (row : E) (active : Finset Pr) (a : Kˣ) :
    Function.HasFiniteMulSupport (fun P : Pr => F P row active a) := by
  have hOrd : {P : Pr | exteriorPrincipalValuation P.val a ≠ 0}.Finite := by
    have h := ((exteriorPrincipalExponentVector a).support.finite_toSet).preimage
      (Subtype.val_injective.injOn : Set.InjOn (Subtype.val : Pr → HeightOneSpectrum (𝓞 K)) _)
    have he : (Subtype.val : Pr → HeightOneSpectrum (𝓞 K)) ⁻¹'
        ↑(exteriorPrincipalExponentVector a).support = {P | exteriorPrincipalValuation P.val a ≠ 0} := by
      ext P
      change P.val ∈ (exteriorPrincipalExponentVector a).support ↔ exteriorPrincipalValuation P.val a ≠ 0
      rw [Finsupp.mem_support_iff, exteriorPrincipalExponentVector_apply]
    exact he ▸ h
  refine ((row.support.finite_toSet.union active.finite_toSet).union hOrd).subset ?_
  intro P hP
  by_contra hn
  have hr : P ∉ row.support := fun h => hn (Or.inl (Or.inl h))
  have ha : P ∉ active := fun h => hn (Or.inl (Or.inr h))
  have ho : exteriorPrincipalValuation P.val a = 0 := by
    by_contra h
    exact hn (Or.inr h)
  exact hP (sourceReflectionSignedExteriorLocal_eq_one_of_outside K S₀ hζ hS row active a P ha hr ho)

theorem sourceReflectionSignedExteriorProduct_eq_prod (row : E) (active : Finset Pr) (a : Kˣ)
    (T : Finset Pr) (hrow : row.support ⊆ T) (hactive : active ⊆ T)
    (hord : ∀ P : Pr, P ∉ T → exteriorPrincipalValuation P.val a = 0) :
    Πext row active a = ∏ P ∈ T, F P row active a := by
  apply finprod_eq_prod_of_mulSupport_subset
  intro P hP
  by_contra hn
  exact hP (sourceReflectionSignedExteriorLocal_eq_one_of_outside K S₀ hζ hS row active a P
    (fun h => hn (hactive h)) (fun h => hn (hrow h)) (hord P hn))

theorem sourceReflectionSignedExteriorProduct_eq_zero_of_local_zero (row : E) (active : Finset Pr) (a : Kˣ)
    (P : Pr) (hP : F P row active a = 0) : Πext row active a = 0 :=
  finprod_eq_zero _ P hP (sourceReflectionSignedExteriorProduct_hasFiniteMulSupport K S₀ hζ hS row active a)

end
end ArtinMatthews.SourceEulerAssembly
