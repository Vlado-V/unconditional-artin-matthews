module

public import ArtinMatthews.SourceReflectionPositiveTwistBranch


set_option backward.privateInPublic true
@[expose] public section

/-! Evaluate the positive finite phase sum directly, including each
support mask. This identity does not use a residual value as a divisor. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic StandardAdelic QuadraticWeil
open scoped NumberField Classical BigOperators AdeleRing

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

local notation "E" => SourcePrimeExponents K S₀
local notation "PE" => SourceExteriorPrime K S₀
local notation "U" => sourceReflectionPositiveTwistAdele K hζ S₀
local notation "wt" => sourceReflectionPositiveTwistWeight K hζ S₀
local notation "φ[" m "," u "]" => finiteCharacter K (algebraMap K 𝔸ᶠ[K] (m:K) * u)

attribute [local instance] positiveTwistResidueFintype positiveTwistLabelFintype

private def positiveTerm (e : E) (x : sourceRing K S₀) (P : e.support)
    (v : (𝓞 K) ⧸ P.val.val.asIdeal) : ℂ :=
  sourceReflectionTameFourierCoefficient K hζ S₀ P.val (sourceReflectionPositiveIndex (e P.val)) v *
    localFiniteCharacter K P.val.val
      ((sourceReflectionPositiveSIntegerAt K S₀ P.val x : P.val.val.adicCompletion K) *
        sourceReflectionPositiveLocalTranslation K hζ S₀ P.val v)

private theorem positiveTerm_product (e : E) (m : Kˣ) (x : sourceRing K S₀)
    (hx : (m:K) = (x:K)) (u : SourceReflectionPositiveTwistLabels K S₀ e) :
    wt e u * φ[m,U e u] = ∏ P : e.support, positiveTerm K hζ S₀ e x P (u P) := by
  let y (P : e.support) := sourceReflectionPositiveSIntegerAt K S₀ P.val x
  have hy (P : e.support) : (y P : P.val.val.adicCompletion K) =
      (sourceKPTraceJacquetFrequencyAt K P.val.val m : P.val.val.adicCompletion K) := by
    change algebraMap K (P.val.val.adicCompletion K) (x:K) = algebraMap K _ (m:K)
    rw [hx]
  rw [sourceReflectionPositiveTwistAdele_character K hζ S₀ e m y hy,
    sourceReflectionPositiveTwistWeight, ← Finset.prod_mul_distrib]
  rfl

theorem sourceReflectionPositiveTwistScalar_eq
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) (e : E) (m : Kˣ)
    (x : sourceRing K S₀) (hx : (m:K) = (x:K)) :
    (∑ u : SourceReflectionPositiveTwistLabels K S₀ e, wt e u * φ[m,U e u]) =
      reflectionExponentResidueValue K hζ S₀ e x := by
  simp_rw [positiveTerm_product K hζ S₀ e m x hx]
  rw [← Fintype.prod_sum (positiveTerm K hζ S₀ e x)]
  let g (P : PE) := sourcePrimeExponentLocalWeight K hζ S₀
    (reflectionPrimeCharacters K hζ S₀) P (e P) x
  change _ = ∏ P ∈ e.support, g P
  rw [← Finset.prod_coe_sort e.support g]
  apply Finset.prod_congr rfl
  intro P _
  exact (sourceReflectionPositiveLocalFourier K hζ S₀ P.val hS
    (sourceReflectionPositiveIndex (e P.val)) (sourceReflectionPositiveSIntegerAt K S₀ P.val x)).trans
    (sourceReflectionPositiveLocalWeight_eq K hζ S₀ P.val _ (Nat.pos_of_ne_zero
      (Finsupp.mem_support_iff.mp P.property)) x)

theorem sourceReflectionPositiveTwistBranchScalar_eq
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) (e : E) (active : Finset PE) (m : Kˣ)
    (x : sourceRing K S₀) (hx : (m:K) = (x:K)) :
    (∑ u : SourceReflectionPositiveTwistLabels K S₀ e,
      (if ∀ P : e.support, u P ≠ 0 ↔ P.val ∈ active then 1 else 0 : ℂ) *
        wt e u * φ[m,U e u]) =
      sourceReflectionPositiveTwistBranchFactor K hζ S₀ e active x := by
  let f (P : e.support) (v : (𝓞 K) ⧸ P.val.val.asIdeal) :=
    if v ≠ 0 ↔ P.val ∈ active then positiveTerm K hζ S₀ e x P v else 0
  have h (u : SourceReflectionPositiveTwistLabels K S₀ e) :
      (if ∀ P : e.support, u P ≠ 0 ↔ P.val ∈ active then 1 else 0 : ℂ) *
          wt e u * φ[m,U e u] = ∏ P : e.support, f P (u P) := by
    by_cases hu : ∀ P : e.support, u P ≠ 0 ↔ P.val ∈ active
    · rw [ite_eq_left hu, one_mul, positiveTerm_product K hζ S₀ e m x hx]
      exact Finset.prod_congr rfl (fun P _ => (ite_eq_left (hu P)).symm)
    · obtain ⟨P,hP⟩ := not_forall.mp hu
      have hz : f P (u P) = 0 := ite_eq_right hP
      rw [ite_eq_right hu, zero_mul, zero_mul, Finset.prod_eq_zero (Finset.mem_univ P) hz]
  simp_rw [h]
  rw [← Fintype.prod_sum f]
  apply Finset.prod_congr rfl
  intro P _
  exact sourceReflectionPositiveLocalFourier_branch K hζ S₀ hS P.val
    (sourceReflectionPositiveIndex (e P.val)) (sourceReflectionPositiveSIntegerAt K S₀ P.val x)
    (P.val ∈ active)

end
end ArtinMatthews
