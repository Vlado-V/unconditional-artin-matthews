module

public import ArtinMatthews.SourceReflectionLocalAngularCharacter
public import ArtinMatthews.SourceReflectionRetainedRay
public import ArtinMatthews.ReflectionCoefficientRow


set_option backward.privateInPublic true
@[expose] public section

/-! The literal local multiplier of the reflected row. The Gauss and
target characters keep their own ray labels. The angular character may
also carry a unitary valuation phase. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain RayClass SourcePhysical AllowedGenerators QuadraticWeil
open scoped NumberField Classical

noncomputable section

variable (F : Type) [Field F] [NumberField F]

theorem sourceReflectionLocalRayCharacter_deep
    (S : Finset (HeightOneSpectrum (𝓞 F))) {M : Ideal (𝓞 F)}
    (ψ : EvenIdealRayCharacter F M) (hM : M ≠ ⊥)
    (u : SFiniteUnits F S)
    (hu : u ∈ sourceReflectionDeepUnits F S (integralIdealFiniteModulus M hM)) :
    sourceReflectionLocalRayCharacter F S ψ hM u = 1 := by
  let n := integralIdealFiniteModulus M hM
  have hq : QuotientGroup.mk' (sourceKPFiniteRaySubgroup F n)
      (sourceReflectionFiniteIdele F S u) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr
      (Subgroup.mem_sup_left (sourceReflectionFiniteIdele_mem_ray_of_deep F S n u hu))
  change sourceReflectionRayValue F ψ hM
    (QuotientGroup.mk' (sourceKPFiniteRaySubgroup F n) (sourceReflectionFiniteIdele F S u)) = 1
  rw [hq, map_one]

theorem sourceReflectionLocalRayCharacter_continuous
    (S : Finset (HeightOneSpectrum (𝓞 F))) {M : Ideal (𝓞 F)}
    (ψ : EvenIdealRayCharacter F M) (hM : M ≠ ⊥) :
    Continuous (sourceReflectionLocalRayCharacter F S ψ hM) :=
  sourceReflectionCharacter_continuous_of_deep F S (integralIdealFiniteModulus M hM) _
    (sourceReflectionLocalRayCharacter_deep F S ψ hM)

variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {J : Ideal (𝓞 F)} (hJ : J ≠ ⊥)
local notation "S" => sourceHilbertSet F S₀
local notation "G" => sixthKummerFixedIdeal S
local notation "hG" => mul_ne_zero (sixthKummerFixedIdeal_ne_zero S) (sixthKummerFixedIdeal_ne_zero S)
local notation "nA" => integralIdealFiniteModulus (sourceReflectionAngularModulus F S₀)
  (sourceReflectionAngularModulus_ne_bot F S₀)
local notation "nG" => integralIdealFiniteModulus (G * G) hG
local notation "nJ" => integralIdealFiniteModulus J hJ

def sourceReflectionThetaModulus : FiniteModulus F := nA + nG + nJ

theorem sourceReflectionThetaModulus_support (hcut : principalAngularCutoff F J ⊆ S) :
    (sourceReflectionThetaModulus F S₀ hJ).support = S := by
  ext P
  have ha := sourceReflectionAngularModulus_support F S₀
  have hg := sourceReflectionGaussModulus_support F S₀
  have hj := sourceReflectionTargetModulus_support F S₀ hJ hcut
  constructor
  · intro hP
    by_contra hn
    have ha0 : nA P = 0 := Finsupp.notMem_support_iff.mp (ha ▸ hn)
    have hg0 : nG P = 0 := Finsupp.notMem_support_iff.mp (by rw [hg]; exact hn)
    have hj0 : nJ P = 0 := Finsupp.notMem_support_iff.mp (fun h => hn (hj h))
    exact (Finsupp.mem_support_iff.mp hP)
      (by simp only [sourceReflectionThetaModulus, Finsupp.add_apply, ha0, hg0, hj0, add_zero])
  · intro hP
    have hn : nA P ≠ 0 := Finsupp.mem_support_iff.mp (ha ▸ hP)
    apply Finsupp.mem_support_iff.mpr
    simp only [sourceReflectionThetaModulus, Finsupp.add_apply]
    omega

variable [IsTotallyComplex F] {ζ : F}

def sourceReflectionLocalThetaCharacter (hJ : J ≠ ⊥) (hζ : IsPrimitiveRoot ζ 12)
    (hBad : standardWeilBadPlaces F ⊆ S) (η : EvenIdealRayCharacter F J) :
    SFiniteUnits F S →* ℂˣ := by
  let gauss : EvenIdealRayCharacter F (G * G) :=
    @sourceGaussHeckeCharacter F _ _ _ ζ hζ S₀ hBad
  exact sourceReflectionLocalAngularCharacter F hζ S₀ *
    sourceReflectionLocalRayCharacter F S gauss hG /
    sourceReflectionLocalRayCharacter F S η hJ

theorem sourceReflectionLocalThetaCharacter_deep (hζ : IsPrimitiveRoot ζ 12)
    (hBad : standardWeilBadPlaces F ⊆ S) (η : EvenIdealRayCharacter F J) (u : SFiniteUnits F S)
    (hu : u ∈ sourceReflectionDeepUnits F S (sourceReflectionThetaModulus F S₀ hJ)) :
    sourceReflectionLocalThetaCharacter F S₀ hJ hζ hBad η u = 1 := by
  let gauss : EvenIdealRayCharacter F (G * G) :=
    @sourceGaussHeckeCharacter F _ _ _ ζ hζ S₀ hBad
  have ha : nA ≤ sourceReflectionThetaModulus F S₀ hJ := by
    intro P
    simp only [sourceReflectionThetaModulus, Finsupp.add_apply]
    omega
  have hg : nG ≤ sourceReflectionThetaModulus F S₀ hJ := by
    intro P
    simp only [sourceReflectionThetaModulus, Finsupp.add_apply]
    omega
  have hj : nJ ≤ sourceReflectionThetaModulus F S₀ hJ := by
    intro P
    simp only [sourceReflectionThetaModulus, Finsupp.add_apply]
    omega
  change sourceReflectionLocalAngularCharacter F hζ S₀ u *
    sourceReflectionLocalRayCharacter F S gauss hG u /
      sourceReflectionLocalRayCharacter F S η hJ u = 1
  rw [sourceReflectionLocalAngularCharacter_deep F hζ S₀ u
      (sourceReflectionDeepUnits_antitone F S ha hu),
    sourceReflectionLocalRayCharacter_deep F S gauss hG u
      (sourceReflectionDeepUnits_antitone F S hg hu),
    sourceReflectionLocalRayCharacter_deep F S η hJ u
      (sourceReflectionDeepUnits_antitone F S hj hu), mul_one, div_one]

theorem sourceReflectionLocalThetaCharacter_continuous (hζ : IsPrimitiveRoot ζ 12)
    (hBad : standardWeilBadPlaces F ⊆ S) (η : EvenIdealRayCharacter F J) :
    Continuous (sourceReflectionLocalThetaCharacter F S₀ hJ hζ hBad η) :=
  sourceReflectionCharacter_continuous_of_deep F S (sourceReflectionThetaModulus F S₀ hJ) _
    (sourceReflectionLocalThetaCharacter_deep F S₀ hJ hζ hBad η)

theorem sourceReflectionLocalThetaCharacter_norm (hζ : IsPrimitiveRoot ζ 12)
    (hBad : standardWeilBadPlaces F ⊆ S) (η : EvenIdealRayCharacter F J) (u : SFiniteUnits F S) :
    ‖(sourceReflectionLocalThetaCharacter F S₀ hJ hζ hBad η u : ℂ)‖ = 1 := by
  let gauss : EvenIdealRayCharacter F (G * G) :=
    @sourceGaussHeckeCharacter F _ _ _ ζ hζ S₀ hBad
  change ‖((sourceReflectionLocalAngularCharacter F hζ S₀ u *
    sourceReflectionLocalRayCharacter F S gauss hG u /
      sourceReflectionLocalRayCharacter F S η hJ u : ℂˣ) : ℂ)‖ = 1
  rw [Units.val_div_eq_div_val, Units.val_mul, norm_div, norm_mul,
    sourceReflectionLocalAngularCharacter_norm F hζ S₀ u,
    sourceReflectionLocalRayCharacter_norm F S gauss hG u,
    sourceReflectionLocalRayCharacter_norm F S η hJ u, mul_one, div_one]

end
end ArtinMatthews.VaryingKummerAnalytic
