module

public import ArtinMatthews.SourceRowHeckeEuler
public import ArtinMatthews.SourceRowKummerNorm


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Kummer and twisted old moduli already omit every prime
of S. Their exterior factors are their literal Dirichlet series, and
the old modulus cost is linear in the actual row norm. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic QuadraticWeil
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "S" => sourceHilbertSet F S₀

theorem sourceKummerSharpIdeal_not_coprime_at_S
    (v : Fˣ) (P : ProbePrime F) (hP : P ∈ S) :
    ¬ IsCoprime P.asIdeal (sixthKummerSharpIdeal S v) := by
  have hd := (dvd_pow_self P.asIdeal (sixthLocalHenselDepth_pos P).ne').trans
    (sixthKummerSharpIdeal_fixed_pow_dvd S v P hP)
  have hle := Ideal.dvd_iff_le.mp hd
  intro h
  have ht := Ideal.isCoprime_iff_sup_eq.mp h
  rw [sup_eq_left.mpr hle] at ht
  exact P.isPrime.ne_top ht

theorem sourceExteriorL_eq_dirichlet_of_mask {M : Ideal (𝓞 F)} (ψ : EvenIdealRayCharacter F M)
    (hψ : ∀ P ∈ S, ψ.allCoefficient P.asIdeal = 0) (s : ℂ) :
    principalAngularExteriorL ψ S s = ψ.dirichlet s := by
  have h : principalAngularRayEulerFactor ψ S s = 1 := by
    unfold principalAngularRayEulerFactor
    apply Finset.prod_eq_one
    intro P hP
    rw [hψ P hP, zero_mul, sub_zero]
  rw [principalAngularExteriorL, h, mul_one]

variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (u : sourceRing F S₀) (hu : u ≠ 0)
local notation "v" => sourceRowFieldUnit F S₀ u hu
local notation "N" => sixthKummerSharpIdeal S v
variable [IsTotallyComplex F]

theorem sourceRowKummerRay_exteriorL (s : ℂ) :
    principalAngularExteriorL (sourceRowKummerRay F hζ S₀ u hu) S s =
      (sourceRowKummerRay F hζ S₀ u hu).dirichlet s :=
  sourceExteriorL_eq_dirichlet_of_mask F S₀ (sourceRowKummerRay F hζ S₀ u hu)
    (fun P hP => (sourceRowKummerRay F hζ S₀ u hu).allCoefficient_eq_zero_of_not_coprime
      P.asIdeal (sourceKummerSharpIdeal_not_coprime_at_S F S₀ v P hP)) s

variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M) (hM : M ≠ ⊥)

theorem sourceRowKummerTwist_exteriorL (s : ℂ) :
    principalAngularExteriorL (sourceRowKummerTwist F hζ S₀ u hu η hM) S s =
      (sourceRowKummerTwist F hζ S₀ u hu η hM).dirichlet s := by
  apply sourceExteriorL_eq_dirichlet_of_mask F S₀
  intro P hP
  apply (sourceRowKummerTwist F hζ S₀ u hu η hM).allCoefficient_eq_zero_of_not_coprime
  intro hc
  exact sourceKummerSharpIdeal_not_coprime_at_S F S₀ v P hP hc.of_mul_right_right

omit [IsTotallyComplex F] in
include hζ in
theorem sourceRowKummerTwist_modulus_norm :
    Ideal.absNorm (M * N) ≤
      Ideal.absNorm M * Ideal.absNorm (sixthKummerFixedIdeal S) *
        sourcePrimeExponentNorm F S₀ (sourceElementExponents F S₀ u hu) := by
  rw [map_mul, mul_assoc]
  exact Nat.mul_le_mul_left _ (sourceRowKummerSharpIdeal_norm_le F hζ S₀ u hu)

theorem sourceGlobalCalF_eq_Hecke_dirichlet
    (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    (hcut : probePrimeCutoff F ⊆ S)
    (ξ w z : ℂ) (hξ : 2 < ξ.re) (hw : 2 < w.re) (hz : 1 / 6 < z.re) :
    sourceGlobalCalF F hζ S₀ hS η u ξ w z =
      principalExteriorZeta S (6 * z) * (sourceRowKummerRay F hζ S₀ u hu).dirichlet w /
      (sourceRowKummerTwist F hζ S₀ u hu η hM).dirichlet ξ *
      sourceGlobalCorrection F hζ S₀ η u hu (ξ, w, z) := by
  rw [sourceGlobalCalF_eq_Hecke F hζ S₀ hS η hM u hu hcut ξ w z hξ hw hz,
    sourceRowKummerRay_exteriorL, sourceRowKummerTwist_exteriorL]

end
end ArtinMatthews.SourceEulerAssembly
