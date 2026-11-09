module

public import ArtinMatthews.AllowedGeneratorBase
public import Mathlib.RingTheory.FractionalIdeal.Extended


set_option backward.privateInPublic true
@[expose] public section

/-! Literal extension from integral-number-ring fractional ideals to
the constructed principal S-integer ring, compatible with principal
field generators and with ordinary ideal extension. -/

namespace ArtinMatthews.AllowedGenerators
open NumberField IsDedekindDomain FractionalIdeal KummerTheory SIntegerPrincipalization
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

private theorem fractionFieldExtension_eq_id (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    (IsFractionRing.map (K := K) (L := K)
      (FaithfulSMul.algebraMap_injective (𝓞 K) (sourceRing K S₀))) = RingHom.id K := by
  apply IsLocalization.ringHom_ext (𝓞 K)⁰
  apply RingHom.ext
  intro x
  change IsFractionRing.map
    (FaithfulSMul.algebraMap_injective (𝓞 K) (sourceRing K S₀))
      (algebraMap (𝓞 K) K x) = algebraMap (𝓞 K) K x
  rw [IsFractionRing.map, IsLocalization.map_eq]
  exact IsScalarTower.algebraMap_apply (𝓞 K) (sourceRing K S₀) K x

def fractionalIdealExtension (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    FractionalIdeal (𝓞 K)⁰ K →+* FractionalIdeal (sourceRing K S₀)⁰ K :=
  FractionalIdeal.extendedHom K (sourceRing K S₀)

theorem fractionalIdealExtension_span (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (a : K) :
    fractionalIdealExtension K S₀ (spanSingleton (𝓞 K)⁰ a) =
      spanSingleton (sourceRing K S₀)⁰ a := by
  simpa only [fractionalIdealExtension, fractionFieldExtension_eq_id, RingHom.id_apply] using
    (extendedHom_spanSingleton (A := 𝓞 K) (K := K) K (sourceRing K S₀) a)

def extendedIdealGroup (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ →* idealGroup K S₀ :=
  Units.map (fractionalIdealExtension K S₀).toMonoidHom

theorem extendedIdealGroup_principal (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (a : Kˣ) :
    extendedIdealGroup K S₀ (toPrincipalIdeal (𝓞 K) K a) =
      toPrincipalIdeal (sourceRing K S₀) K a := by
  apply Units.ext
  simp only [extendedIdealGroup, Units.coe_map, coe_toPrincipalIdeal]
  change fractionalIdealExtension K S₀ (spanSingleton (𝓞 K)⁰ (a : K)) = _
  exact fractionalIdealExtension_span K S₀ (a : K)

theorem extendedIdealGroup_integral (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (I : (Ideal (𝓞 K))⁰) :
    (extendedIdealGroup K S₀ (FractionalIdeal.mk0 K I) :
      FractionalIdeal (sourceRing K S₀)⁰ K) =
      (I.val.map (algebraMap (𝓞 K) (sourceRing K S₀)) :
        FractionalIdeal (sourceRing K S₀)⁰ K) :=
  extendedHom_coeIdeal_eq_map K (sourceRing K S₀) I.val

theorem extendedIdealGroup_exterior (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (I : exteriorIdeals (principalizingDenominator (sourceHilbertSeed K S₀))) :
    (extendedIdealGroup K S₀ (FractionalIdeal.mk0 K ⟨I.val, by
      exact mem_nonZeroDivisors_iff_ne_zero.mpr I.property.1⟩) :
      FractionalIdeal (sourceRing K S₀)⁰ K) =
      ((show Ideal (sourceRing K S₀) from
        (principalExteriorIdealEquiv (sourceHilbertSeed K S₀) I).val) :
        FractionalIdeal (sourceRing K S₀)⁰ K) :=
  extendedHom_coeIdeal_eq_map K (sourceRing K S₀) I.val

end
end ArtinMatthews.AllowedGenerators
