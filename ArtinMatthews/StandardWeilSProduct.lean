module

public import ArtinMatthews.StandardTameFiniteWeil
public import ArtinMatthews.SLocalHilbertGlobalClass


set_option backward.privateInPublic true
@[expose] public section

/-! The actual S-product Weil cocycle. It is derived from the genuine
global analytic product and global Hilbert reciprocity, using tame local
comparison only outside the fixed different/two cutoff. -/

namespace ArtinMatthews.QuadraticWeil

open NumberField IsDedekindDomain ClassFieldTheory
open ArtinMatthews.QuadraticGauss
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]

omit [IsTotallyComplex F] in
theorem globalWeilHilbertRatio_finite_outside (a b : Fˣ) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ standardWeilBadPlaces F) : globalWeilHilbertRatio F a b (.inr v) = 1 := by
  unfold globalWeilHilbertRatio
  change (standardNormalizedWeil F a (.inr v) * standardNormalizedWeil F b (.inr v)) /
    (standardNormalizedWeil F (a * b) (.inr v) * finiteQuadraticHilbertSign F a b v) = 1
  rw [mul_comm (standardNormalizedWeil F (a * b) (.inr v)),
    ← standardNormalizedWeil_finite_cocycle F a b v hv]
  exact div_self (mul_ne_zero (standardNormalizedWeil_ne_zero F a (.inr v))
    (standardNormalizedWeil_ne_zero F b (.inr v)))

theorem globalWeilHilbertRatio_prod_S (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : standardWeilBadPlaces F ⊆ S) (a b : Fˣ) :
    ∏ v ∈ S, globalWeilHilbertRatio F a b (.inr v) = 1 := by
  let T : Finset (ArchimedeanAdeles.Construction.Places F) := S.image Sum.inr
  have hout : ∀ v ∉ T, globalWeilHilbertRatio F a b v = 1 := by
    intro v hv
    cases v with
    | inl v => exact globalWeilHilbertRatio_infinite F a b v
    | inr v =>
        apply globalWeilHilbertRatio_finite_outside F a b v
        intro hbad
        exact hv (Finset.mem_image.mpr ⟨v, hS hbad, rfl⟩)
  have hprod : ∏ v ∈ T, globalWeilHilbertRatio F a b v = 1 :=
    (hasProd_prod_of_ne_finset_one hout).unique (globalWeilHilbertRatio_hasProd F a b)
  dsimp only [T] at hprod
  rwa [Finset.prod_image (fun _ _ _ _ h => Sum.inr_injective h)] at hprod

theorem standardNormalizedWeil_S_cocycle (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : standardWeilBadPlaces F ⊆ S) (a b : Fˣ) :
    (∏ v : S, standardNormalizedWeil F a (.inr v.1)) *
        (∏ v : S, standardNormalizedWeil F b (.inr v.1)) =
      (∏ v : S, finiteQuadraticHilbertSign F a b v.1) *
        (∏ v : S, standardNormalizedWeil F (a * b) (.inr v.1)) := by
  have h := globalWeilHilbertRatio_prod_S F S hS a b
  simp only [globalWeilHilbertRatio, allPlaceQuadraticHilbertSign,
    Finset.prod_div_distrib, Finset.prod_mul_distrib] at h
  have hsign (v : HeightOneSpectrum (𝓞 F)) : finiteQuadraticHilbertSign F a b v ≠ 0 := by
    have hsq : finiteQuadraticHilbertSign F a b v ^ 2 = 1 := rootSign_sq F _
    intro he
    rw [he, zero_pow (by decide)] at hsq
    exact zero_ne_one hsq
  have hden : (∏ v ∈ S, standardNormalizedWeil F (a * b) (.inr v)) *
      (∏ v ∈ S, finiteQuadraticHilbertSign F a b v) ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun v _ => standardNormalizedWeil_ne_zero F (a * b) (.inr v)))
      (Finset.prod_ne_zero_iff.mpr (fun v _ => hsign v))
  have he := (div_eq_iff hden).mp h
  rw [one_mul] at he
  simpa only [← Finset.prod_coe_sort S (fun v => standardNormalizedWeil F a (.inr v)),
    ← Finset.prod_coe_sort S (fun v => standardNormalizedWeil F b (.inr v)),
    ← Finset.prod_coe_sort S (fun v => standardNormalizedWeil F (a * b) (.inr v)),
    ← Finset.prod_coe_sort S (finiteQuadraticHilbertSign F a b)] using he.trans (mul_comm _ _)

theorem sLocalAnalyticWeil_cocycle (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : standardWeilBadPlaces F ⊆ S) (x y : SLocalPowerClasses F 2 S) :
    sLocalAnalyticWeil F S x * sLocalAnalyticWeil F S y =
      rootSign F (sLocalHilbertForm F 2 (numberFieldQuadraticRoots F) S x y) *
        sLocalAnalyticWeil F S (x * y) := by
  obtain ⟨a, rfl⟩ := sLocalGlobalClassMap_surjective F 2 (numberFieldQuadraticRoots F) S x
  obtain ⟨b, rfl⟩ := sLocalGlobalClassMap_surjective F 2 (numberFieldQuadraticRoots F) S y
  rw [← map_mul (sLocalGlobalClassMap F 2 S), sLocalAnalyticWeil_globalClass, sLocalAnalyticWeil_globalClass,
    sLocalAnalyticWeil_globalClass, sLocalHilbertSign_globalClass]
  exact standardNormalizedWeil_S_cocycle F S hS a b

end

end ArtinMatthews.QuadraticWeil
