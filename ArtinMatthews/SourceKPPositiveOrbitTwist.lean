module

public import ArtinMatthews.SourceKPPositiveSeedPhysicalCoefficient
public import ArtinMatthews.SourceReflectionPositiveTwistScalar
public import ArtinMatthews.SourceSixthUnitResidue


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite positive twist on each allowed orbit depends on
the literal exterior numerator, including when the twist is restricted
to a fixed active support. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators SourcePhysical VaryingKummerAnalytic QuadraticWeil
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "E" => SourcePrimeExponents K S₀
local notation "C" => ReflectionSquarefreeExponents K S₀
local notation "Γ" => sNormOneSixthSubgroup K S
local notation "freq" => sourceKPAllowedSquarefreeCubeFieldEquiv K hζ S₀
local notation "gen" => sourcePrimeExponentGenerator K hζ S₀

attribute [local instance] positiveTwistLabelFintype

theorem sourceKPAllowedSquarefreeCubeFieldEquiv_integer (c : C) (n : E) (γ : Γ) :
    ∃ r : exteriorUnitSubgroup S,
      ((freq ((c,n),γ)).val : K) =
        ((gen (c.val + 3 • n) * (sourceExteriorUnitToSourceRing K S₀ r)^6 : sourceRing K S₀) : K) := by
  obtain ⟨r,hr⟩ := sourceExteriorUnitSixthPower_exists_root S
    ((sourceExteriorSixthNormOneEquiv K S).symm γ)
  have he := congrArg (fun v : exteriorUnitSubgroup S => v.val) hr
  refine ⟨r,?_⟩
  rw [sourceKPAllowedSquarefreeCubeFieldEquiv_fieldUnit K hζ S₀ c n γ, he, Subgroup.coe_pow,
    Units.val_mul, Units.val_pow_eq_pow_val, sourcePrimeExponentUnit_val,
    Subalgebra.coe_mul, Subalgebra.coe_pow, sourceExteriorUnitToSourceRing_val]

theorem sourceKPPositivePhysicalTwistScalar_orbit (hS : standardWeilBadPlaces K ⊆ S)
    (e : E) (c : C) (n : E) (γ : Γ) :
    sourceKPPositivePhysicalTwistScalar K hζ S₀ e (fun _ => 1) (freq ((c,n),γ)).val =
      reflectionExponentResidueValue K hζ S₀ e (gen (c.val + 3 • n)) := by
  obtain ⟨r,hr⟩ := sourceKPAllowedSquarefreeCubeFieldEquiv_integer K hζ S₀ c n γ
  unfold sourceKPPositivePhysicalTwistScalar
  simp only [one_mul]
  rw [sourceReflectionPositiveTwistScalar_eq K hζ S₀ hS e _ _ hr]
  exact reflectionExponentResidueValue_mul_sixth K S₀ hζ e (gen (c.val + 3 • n))
    (sourceExteriorUnitToSourceUnits K S₀ r)

def sourceKPPositivePhysicalActiveMask (e : E) (active : Finset (SourceExteriorPrime K S₀))
    (h : SourceReflectionPositiveTwistLabels K S₀ e) : ℂ :=
  if ∀ P : e.support, h P ≠ 0 ↔ P.val ∈ active then 1 else 0

theorem sourceKPPositivePhysicalTwistScalar_branch_orbit (hS : standardWeilBadPlaces K ⊆ S)
    (e : E) (active : Finset (SourceExteriorPrime K S₀)) (c : C) (n : E) (γ : Γ) :
    sourceKPPositivePhysicalTwistScalar K hζ S₀ e (sourceKPPositivePhysicalActiveMask K S₀ e active)
        (freq ((c,n),γ)).val =
      sourceReflectionPositiveTwistBranchFactor K hζ S₀ e active (gen (c.val + 3 • n)) := by
  obtain ⟨r,hr⟩ := sourceKPAllowedSquarefreeCubeFieldEquiv_integer K hζ S₀ c n γ
  unfold sourceKPPositivePhysicalTwistScalar sourceKPPositivePhysicalActiveMask
  rw [sourceReflectionPositiveTwistBranchScalar_eq K hζ S₀ hS e active _ _ hr,
    sourceReflectionPositiveTwistBranchFactor_sixth K hζ S₀ e active _ r]

end
end ArtinMatthews
