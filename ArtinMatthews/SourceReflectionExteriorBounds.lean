module

public import ArtinMatthews.SourceReflectionExteriorFactors


set_option backward.privateInPublic true
@[expose] public section

/-! The frozen coefficient carries the full local weight. The row and
column factors are bounded by one on their separate supports. -/

namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic StandardAdelic QuadraticWeil
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
  {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
  (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)

local notation "S" => sourceHilbertSet K S₀
local notation "Pr" => SourceExteriorPrime K S₀
local notation "E" => SourcePrimeExponents K S₀
local notation "U" => exteriorUnitSubgroup S
local notation "D" => sourceReflectionDirectedCofactor K S₀ hζ
local notation "F" => sourceReflectionSphericalFixedPhase K S₀ hζ
local notation "A" => sourceReflectionActiveFixedPhase K S₀ hζ
local notation "q" => sourceReflectionPrimeNorm K S₀

private theorem sphericalFixedPhase_norm (ε : U) (f : Finset Pr) (a : E) (P : Pr) :
    ‖(F ε f a P : ℂ)‖ = 1 := by
  simp only [sourceReflectionSphericalFixedPhase, Units.val_mul, norm_mul,
    Units.val_zpow_eq_zpow_val, norm_zpow, sourceReflectionTameUnitCharacter_norm,
    sourceReflectionDirectedCofactor_norm, one_zpow, mul_one]

private theorem activeFixedPhase_norm (ε : U) (f : Finset Pr) (a n : E) (P : Pr) :
    ‖(A ε f a n P : ℂ)‖ = 1 := by
  simp only [sourceReflectionActiveFixedPhase, Units.val_mul, norm_mul,
    Units.val_pow_eq_pow_val, norm_pow, sphericalFixedPhase_norm,
    sourceReflectionDirectedCofactor_norm, one_pow, mul_one]

private theorem inactive_norm_le_one (P : Pr) :
    ‖sourceReflectionExteriorInactiveFactor K S₀ P‖ ≤ 1 := by
  have hq : (1 : ℝ) ≤ (Ideal.absNorm P.val.asIdeal : ℝ) :=
    one_le_two.trans (sourceReflection_primeNorm_two_le K S₀ P)
  have hp : (0 : ℝ) < Ideal.absNorm P.val.asIdeal := zero_lt_one.trans_le hq
  have hi : (Ideal.absNorm P.val.asIdeal : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq
  rw [sourceReflectionExteriorInactiveFactor, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr hi)]
  exact sub_le_self _ (inv_nonneg.mpr hp.le)

private theorem frozenPrime_norm_le (ε : U) (h : E) (f : Finset Pr) (a n : E) (P : Pr) :
    ‖sourceReflectionExteriorFrozenPrime K S₀ hζ hS ε h f a n P‖ ≤
      sourceReflectionFrozenLocalWeight (q P) (a P) := by
  rw [sourceReflectionExteriorFrozenPrime, norm_mul, Units.val_zpow_eq_zpow_val,
    norm_zpow, activeFixedPhase_norm, one_zpow, mul_one]
  exact sourceReflectionTameRotatedActive_norm_le_frozen K hζ S₀ P hS _ _ 1
    (1 : sourceReflectionTameValuationUnits K S₀ P).property

theorem sourceReflectionExteriorFrozen_norm_le (ε : U) (h : E) (f : Finset Pr) (a n : E) :
    ‖sourceReflectionExteriorFrozen K S₀ hζ hS ε h f a n‖ ≤ sourceReflectionFrozenWeight K S₀ f a := by
  have hi : ‖∏ P ∈ h.support \ f, sourceReflectionExteriorInactiveFactor K S₀ P‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun P _ => inactive_norm_le_one K S₀ P)
  have hf : ‖∏ P ∈ f, sourceReflectionExteriorFrozenPrime K S₀ hζ hS ε h f a n P‖ ≤
      sourceReflectionFrozenWeight K S₀ f a := by
    rw [norm_prod, sourceReflectionFrozenWeight]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      (fun P _ => frozenPrime_norm_le K S₀ hζ hS ε h f a n P)
  rw [sourceReflectionExteriorFrozen, norm_mul]
  exact (mul_le_mul_of_nonneg_right hi (norm_nonneg _)).trans (by rwa [one_mul])

private theorem rowPrime_norm (ε : U) (f : Finset Pr) (a n d : E) (P : Pr) :
    ‖sourceReflectionExteriorRowPrime K S₀ hζ hS ε f a n d P‖ = 1 := by
  rw [sourceReflectionExteriorRowPrime, norm_mul, Units.val_mul, norm_mul,
    activeFixedPhase_norm, Units.val_zpow_eq_zpow_val, norm_zpow,
    sourceReflectionDirectedCofactor_norm, one_zpow, mul_one, mul_one,
    sourceReflectionTameRotatedActive_norm_eq K hζ S₀ P hS 1 0 1
      (1 : sourceReflectionTameValuationUnits K S₀ P).property]
  norm_num

private theorem rowActivePhase_norm (h a d : E) (P : Pr) :
    ‖sourceReflectionExteriorRowActivePhase K S₀ hζ h a d P‖ = 1 := by
  simp only [sourceReflectionExteriorRowActivePhase, Units.val_zpow_eq_zpow_val,
    norm_zpow, sourceReflectionDirectedCofactor_norm, one_zpow]

theorem sourceReflectionExteriorRow_norm_le_one (ε : U) (h : E) (f : Finset Pr) (a n d : E) :
    ‖sourceReflectionExteriorRow K S₀ hζ hS ε h f a n d‖ ≤ 1 := by
  unfold sourceReflectionExteriorRow
  split_ifs
  · rw [norm_mul, norm_prod, norm_prod]
    simp only [rowPrime_norm K S₀ hζ hS, rowActivePhase_norm K S₀ hζ,
      Finset.prod_const_one, one_mul, le_refl]
  · simp

private theorem prime_cross_norm (P Q : Pr) :
    ‖(sourcePrimeCrossDiagonalUnit K hζ S₀ P Q : ℂ)‖ = 1 := by
  apply Complex.norm_eq_one_of_mem_rootsOfUnity (n := 6)
  rw [mem_rootsOfUnity]
  exact sourcePrimeCrossDiagonalUnit_pow_six K hζ S₀ P Q

include hS in
private theorem gammaTwo_norm (c : ReflectionSquarefreeExponents K S₀) :
    ‖reflectionGammaTwo K hζ S₀ c.val‖ = 1 := by
  rw [reflectionGammaTwo_eq_normalized_support, reflectionGaussDirectedPairs_support, norm_mul]
  have hp : ‖∏ P ∈ c.val.support, ∏ Q ∈ c.val.support, reflectionGaussPairKernel K hζ S₀ c P Q‖ = 1 := by
    rw [norm_prod]
    apply Finset.prod_eq_one
    intro P _
    rw [norm_prod]
    apply Finset.prod_eq_one
    intro Q _
    rw [reflectionGaussPairKernel_unit K hζ S₀ c P Q, Units.val_pow_eq_pow_val,
      norm_pow, prime_cross_norm K S₀ hζ P Q, one_pow]
  have hg : ‖∏ P : c.val.support, reflectionNormalizedPrimeGamma K hζ S₀ P.val‖ = 1 := by
    rw [norm_prod]
    apply Finset.prod_eq_one
    intro P _
    rw [← sourceJacquetActualGauss_two_eq_gamma, sourceJacquetActualGauss_norm K hζ S₀ P.val hS 2 (by decide)]
  rw [hp, hg, one_mul]

include hS in
theorem sourceReflectionExteriorColumn_norm_le_one (ε : U) (h : E) (f : Finset Pr) (a c : E) :
    ‖sourceReflectionExteriorColumn K S₀ hζ ε h f a c‖ ≤ 1 := by
  unfold sourceReflectionExteriorColumn
  by_cases hc : SourceReflectionExteriorColumnSupport K S₀ f c
  · rw [ite_eq_left hc, norm_mul, norm_mul, norm_prod, norm_prod,
      gammaTwo_norm K S₀ hζ hS ⟨c,hc.1⟩]
    simp only [sourceReflectionExteriorColumnActivePhase, sourceReflectionExteriorColumnPrime,
      Units.val_zpow_eq_zpow_val, norm_zpow, sourceReflectionDirectedCofactor_norm, one_zpow,
      Units.val_pow_eq_pow_val, norm_pow, sphericalFixedPhase_norm, one_pow,
      Finset.prod_const_one, one_mul, le_refl]
  · simp [hc]

end
end ArtinMatthews.SourceEulerAssembly
