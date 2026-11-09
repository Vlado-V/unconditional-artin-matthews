module

public import ArtinMatthews.SLocalPaperHilbertNormalization


set_option backward.privateInPublic true
@[expose] public section

/-! A consistent actual choice of the source isotropic complement and
the actual principal S-integer ring. The principal fractional-ideal
kernel is identified with genuine S-units. -/

namespace ArtinMatthews.AllowedGenerators
open NumberField IsDedekindDomain FractionalIdeal KummerTheory SIntegerPrincipalization
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

abbrev sourceRing (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :=
  IntegerRing (K := K) (sourceHilbertSet K S₀)

instance sourceRing_fractionField (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    IsFractionRing (sourceRing K S₀) K :=
  principalIntegerRing_isFractionRing (sourceHilbertSeed K S₀)

instance sourceRing_dedekind (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    IsDedekindDomain (sourceRing K S₀) :=
  principalIntegerRing_isDedekindDomain (sourceHilbertSeed K S₀)

instance sourceRing_principal (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    IsPrincipalIdealRing (sourceRing K S₀) := sourceHilbertSet_isPrincipalIdealRing K S₀

abbrev idealGroup (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :=
  (FractionalIdeal (sourceRing K S₀)⁰ K)ˣ

def chosenB {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup (SLocalRingPowerClasses K 6 (sourceHilbertSet K S₀)) :=
  (source_paper_sixth_isotropic_complement K hζ S₀).choose

theorem chosenB_isCompl {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    IsCompl (sLocalRingUnitImage K 6 (sourceHilbertSet K S₀)) (chosenB K hζ S₀) :=
  (source_paper_sixth_isotropic_complement K hζ S₀).choose_spec.1

theorem chosenB_isotropic {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∀ x ∈ chosenB K hζ S₀, ∀ y ∈ chosenB K hζ S₀,
      paperSourceHilbertForm K hζ (sourceHilbertSet K S₀) x y = 1 :=
  (source_paper_sixth_isotropic_complement K hζ S₀).choose_spec.2

def allowedSubgroup {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) : Subgroup Kˣ :=
  (chosenB K hζ S₀).comap (sLocalRingGlobalClassMap K 6 (sourceHilbertSet K S₀))

@[simp] theorem mem_allowedSubgroup {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (a : Kˣ) :
    a ∈ allowedSubgroup K hζ S₀ ↔
      sLocalRingGlobalClassMap K 6 (sourceHilbertSet K S₀) a ∈ chosenB K hζ S₀ := Iff.rfl

def unitEquivInteger (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    SUnitGroup (K := K) (sourceHilbertSet K S₀) ≃* (sourceRing K S₀)ˣ :=
  Set.unitEquivUnitsInteger (↑(sourceHilbertSet K S₀) : Set (HeightOneSpectrum (𝓞 K))) K

def fieldUnitMap (S₀ : Finset (HeightOneSpectrum (𝓞 K))) : (sourceRing K S₀)ˣ →* Kˣ :=
  Units.map (algebraMap (sourceRing K S₀) K).toMonoidHom

@[simp] theorem fieldUnitMap_unitEquiv (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (u : SUnitGroup (K := K) (sourceHilbertSet K S₀)) :
    fieldUnitMap K S₀ (unitEquivInteger K S₀ u) = (u : Kˣ) := rfl

@[simp] theorem unitEquiv_symm_coe (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (u : (sourceRing K S₀)ˣ) :
    ((unitEquivInteger K S₀).symm u : Kˣ) = fieldUnitMap K S₀ u := by
  apply Units.ext
  rfl

theorem sUnit_principal_eq_one (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (u : SUnitGroup (K := K) (sourceHilbertSet K S₀)) :
    toPrincipalIdeal (sourceRing K S₀) K (u : Kˣ) = 1 := by
  let w := unitEquivInteger K S₀ u
  apply Units.ext
  rw [coe_toPrincipalIdeal, Units.val_one, ← spanSingleton_one]
  apply spanSingleton_eq_spanSingleton.mpr
  refine ⟨w⁻¹, ?_⟩
  change algebraMap (sourceRing K S₀) K (↑(w⁻¹)) * ((u : Kˣ) : K) = 1
  have hw : algebraMap (sourceRing K S₀) K (w : sourceRing K S₀) = ((u : Kˣ) : K) := rfl
  rw [← hw, ← map_mul, Units.inv_mul, map_one]

theorem principal_eq_one_iff_sUnit (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (a : Kˣ) :
    toPrincipalIdeal (sourceRing K S₀) K a = 1 ↔
      a ∈ SUnitGroup (K := K) (sourceHilbertSet K S₀) := by
  constructor
  · intro ha
    have hs : spanSingleton (sourceRing K S₀)⁰ (a : K) =
        spanSingleton (sourceRing K S₀)⁰ (1 : K) := by
      have h := congrArg Units.val ha
      simpa only [coe_toPrincipalIdeal, Units.val_one, spanSingleton_one] using h
    obtain ⟨u, hu⟩ := spanSingleton_eq_spanSingleton.mp hs
    have hmul : fieldUnitMap K S₀ u * a = 1 := Units.ext hu
    have h := congrArg (fun x : Kˣ => (fieldUnitMap K S₀ u)⁻¹ * x) hmul
    have he : a = (fieldUnitMap K S₀ u)⁻¹ := by
      simpa only [← mul_assoc, inv_mul_cancel, one_mul, mul_one] using h
    rw [he]
    have huS := ((unitEquivInteger K S₀).symm (u⁻¹)).property
    change fieldUnitMap K S₀ (u⁻¹) ∈ SUnitGroup (K := K) (sourceHilbertSet K S₀) at huS
    simpa only [map_inv] using huS
  · intro ha
    exact sUnit_principal_eq_one K S₀ ⟨a, ha⟩

theorem principal_eq_iff_ratio_sUnit (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (a b : Kˣ) :
    toPrincipalIdeal (sourceRing K S₀) K a = toPrincipalIdeal (sourceRing K S₀) K b ↔
      a / b ∈ SUnitGroup (K := K) (sourceHilbertSet K S₀) := by
  rw [← principal_eq_one_iff_sUnit K S₀ (a / b), map_div, div_eq_one]

end
end ArtinMatthews.AllowedGenerators
