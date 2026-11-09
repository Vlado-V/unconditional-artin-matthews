module

public import ArtinMatthews.SourceFullIdealEuler
public import ArtinMatthews.SourceGlobalEulerExtraction


set_option backward.privateInPublic true
@[expose] public section

/-! Exact deletion of the literal finite source set from the full
Dedekind and ray Euler products. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

theorem sourceExteriorValueEuler_delete (a : ProbePrime F → ℂ) (ha : ∀ P, ‖a P‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) (L : ℂ)
    (hL : HasProd (fun P : ProbePrime F => (1 - sourcePrimeEulerRatio F P (a P) s)⁻¹) L) :
    sourceExteriorValueEuler F S₀ (fun P => a P.val) s =
      L * ∏ P ∈ sourceHilbertSet F S₀, (1 - sourcePrimeEulerRatio F P (a P) s) := by
  let S := sourceHilbertSet F S₀
  let f (P : ProbePrime F) := 1 - sourcePrimeEulerRatio F P (a P) s
  let B := ∏ P ∈ S, f P
  let E := sourceExteriorValueEuler F S₀ (fun P => a P.val) s
  have hExt : HasProd (fun P : SourceExteriorPrime F S₀ => (f P.val)⁻¹) E :=
    sourceExteriorValueEuler_hasProd F S₀ (fun P => a P.val) (fun P => ha P.val) s hs
  have hFin : HasProd (fun P : S => (f P.val)⁻¹) (∏ P ∈ S, (f P)⁻¹) :=
    S.hasProd (fun P => (f P)⁻¹)
  have hAll : HasProd (fun P : ProbePrime F => (f P)⁻¹) ((∏ P ∈ S, (f P)⁻¹) * E) :=
    hFin.mul_compl hExt
  have hEq : B⁻¹ * E = L := by
    change (∏ P ∈ S, f P)⁻¹ * E = L
    rw [← Finset.prod_inv_distrib]
    exact hAll.unique hL
  have hB : B ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun P _ =>
    sourceOneSub_ne_zero_of_norm_lt_one ((sourcePrimeEulerRatio_norm_le_half F P (a P) s
      (ha P) hs.le).trans_lt (by norm_num)))
  change E = L * B
  rw [← hEq, mul_comm B⁻¹ E, mul_assoc, inv_mul_cancel₀ hB, mul_one]

theorem sourceExteriorValueEuler_eq_angularL {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M)
    (s : ℂ) (hs : 1 < s.re) :
    sourceExteriorValueEuler F S₀ (fun P => η.allCoefficient P.val.asIdeal) s =
      principalAngularExteriorL η (sourceHilbertSet F S₀) s := by
  simpa only [principalAngularExteriorL, principalAngularRayEulerFactor, sourcePrimeEulerRatio] using
    sourceExteriorValueEuler_delete F S₀ (fun P => η.allCoefficient P.asIdeal)
      (fun P => η.allCoefficient_norm_le_one P.asIdeal) s hs _ (sourceFullRayEuler_hasProd F η s hs)

theorem sourceExteriorValueEuler_eq_exteriorZeta (s : ℂ) (hs : 1 < s.re) :
    sourceExteriorValueEuler F S₀ (fun _ => 1) s =
      principalExteriorZeta (sourceHilbertSet F S₀) s := by
  simpa only [principalExteriorZeta, principalZetaEulerFactor, sourcePrimeEulerRatio,
    mixedDedekindZeta_eq F hs, one_mul] using
    sourceExteriorValueEuler_delete F S₀ (fun _ => 1) (fun _ => by simp) s hs _
      (sourceFullDedekindEuler_hasProd F s hs)

end
end ArtinMatthews.SourceEulerAssembly
