module

public import ArtinMatthews.SLocalHilbertForm
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.MaximalKummerNorm


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine global representatives of every finite tuple of local power
classes. Openness of local powers follows from actual Kummer norm groups;
the surjection is genuine multiplicative weak approximation. -/

namespace ArtinMatthews

open NumberField IsDedekindDomain KummerTheory ClassFieldTheory LocalClassFieldTheory
open scoped NumberField Classical
noncomputable section

theorem localPowerRange_isOpen (F : Type) [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (n : ℕ+) (hnF : ((n : ℕ) : F) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty) :
    IsOpen ((powMonoidHom (n : ℕ) : Fˣ →* Fˣ).range : Set Fˣ) := by
  let E := kummerRadicalExtension (K := F) (Omega := SeparableClosure F) n
    (maximalKummerSubgroup F n).1
  let : FiniteDimensional F E :=
    maximalKummerRadicalExtension_finiteDimensional (K := F) n hnF hmu
  let : IsGalois F E := kummerRadicalExtension_isGalois n _
  have h := maximalKummerNormSubgroup_eq_powMonoidHom_range
    (K := F) (Omega := SeparableClosure F) n hnF hmu
  rw [← h]
  exact localNormSubgroup_isOpen F E

variable (K : Type) [Field K] [NumberField K]

theorem finitePlace_powerRange_isOpen (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) :
    IsOpen ((powMonoidHom (n : ℕ) : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range :
      Set (v.adicCompletion K)ˣ) := by
  let C := v.adicCompletion K
  let : ValuativeRel C := finitePlaceCompletionValuativeRel K v
  let : IsNonarchimedeanLocalField C := finitePlaceCompletionIsNonarchimedeanLocalField K v
  have hnC : ((n : ℕ) : C) ≠ 0 := Nat.cast_ne_zero.mpr n.ne_zero
  have hmuC : (primitiveRoots (n : ℕ) C).Nonempty := by
    obtain ⟨ζ, hζ⟩ := hmu
    exact ⟨algebraMap K C ζ, (mem_primitiveRoots n.pos).mpr
      (((mem_primitiveRoots n.pos).mp hζ).map_of_injective (algebraMap K C).injective)⟩
  exact localPowerRange_isOpen C n hnC hmuC

def sLocalGlobalClassMap (n : ℕ+) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Kˣ →* SLocalPowerClasses K n S :=
  MonoidHom.pi fun v => (powerClass (v.1.adicCompletion K) n).comp
    (Units.map (algebraMap K (v.1.adicCompletion K)).toMonoidHom)

theorem sLocalGlobalClassMap_surjective (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) : Function.Surjective (sLocalGlobalClassMap K n S) := by
  have h := IdeleGroup.principalLocalQuotientMap_surjective S
    (fun v => (powMonoidHom (n : ℕ) : (v.1.adicCompletion K)ˣ →* (v.1.adicCompletion K)ˣ).range)
    (fun v => finitePlace_powerRange_isOpen K n hmu v.1)
  intro y
  obtain ⟨a, ha⟩ := h y
  refine ⟨a, ?_⟩
  funext v
  exact congrFun ha v

@[simp] theorem sLocalGlobalClassMap_sUnit (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (u : SUnitGroup (K := K) S) :
    sLocalGlobalClassMap K n S (u : Kˣ) = sLocalUnitClassMap K n S u := rfl

end
end ArtinMatthews
