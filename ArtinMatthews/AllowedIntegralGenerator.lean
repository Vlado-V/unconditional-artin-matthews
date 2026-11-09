module

public import ArtinMatthews.AllowedGeneratorSelection
public import ArtinMatthews.AllowedIdealExtension


set_option backward.privateInPublic true
@[expose] public section

/-! Every genuine exterior integral ideal has an allowed generator in
the actual S-integer ring. No generator or principality premise is used. -/

namespace ArtinMatthews.AllowedGenerators
open NumberField IsDedekindDomain FractionalIdeal KummerTheory SIntegerPrincipalization
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

theorem exists_integral_allowed_generator {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (I : (Ideal (sourceRing K S₀))⁰) :
    ∃ a : sourceRing K S₀, ∃ ha : a ≠ 0,
      I.val = Ideal.span {a} ∧
      Units.mk0 (a : K) (by exact (Subtype.coe_injective.ne ha)) ∈ allowedSubgroup K hζ S₀ := by
  obtain ⟨a, ha, hB⟩ := exists_allowed_generator K hζ S₀ (FractionalIdeal.mk0 K I)
  have heq : spanSingleton (sourceRing K S₀)⁰ (a : K) =
      (I.val : FractionalIdeal (sourceRing K S₀)⁰ K) := by
    have h := congrArg Units.val ha
    simpa only [coe_toPrincipalIdeal, coe_mk0] using h
  have hmem : (a : K) ∈ (I.val : FractionalIdeal (sourceRing K S₀)⁰ K) :=
    heq ▸ mem_spanSingleton_self (sourceRing K S₀)⁰ (a : K)
  obtain ⟨b, hb, hba⟩ := (mem_coeIdeal (sourceRing K S₀)⁰).mp hmem
  have hb0 : b ≠ 0 := by
    intro he
    apply a.ne_zero
    rw [← hba, he, map_zero]
  refine ⟨b, hb0, ?_, ?_⟩
  · apply FractionalIdeal.coeIdeal_injective (K := K)
    change (I.val : FractionalIdeal (sourceRing K S₀)⁰ K) =
      (Ideal.span {b} : FractionalIdeal (sourceRing K S₀)⁰ K)
    rw [coeIdeal_span_singleton, hba]
    exact heq.symm
  · have hunit : Units.mk0 (b : K) (by exact (Subtype.coe_injective.ne hb0)) = a :=
      Units.ext hba
    rw [hunit]
    exact hB

theorem exists_exterior_allowed_generator {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (I : exteriorIdeals (principalizingDenominator (sourceHilbertSeed K S₀))) :
    ∃ a : sourceRing K S₀, ∃ ha : a ≠ 0,
      I.val.map (algebraMap (𝓞 K) (sourceRing K S₀)) = Ideal.span {a} ∧
      Units.mk0 (a : K) (by exact (Subtype.coe_injective.ne ha)) ∈ allowedSubgroup K hζ S₀ :=
  exists_integral_allowed_generator K hζ S₀
    (principalExteriorIdealEquiv (sourceHilbertSeed K S₀) I)

end
end ArtinMatthews.AllowedGenerators
