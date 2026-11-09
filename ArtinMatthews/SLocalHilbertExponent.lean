module

public import ArtinMatthews.PowerClassSixthCRT
public import ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertExponentCompatibility


set_option backward.privateInPublic true
@[expose] public section

/-! The actual local Artin symbols at exponents two and three are the
third and second powers of the actual sextic symbol. Global weak
approximation transports this identity to every actual S-local class. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain KummerTheory ClassFieldTheory
open GlobalClassFieldTheory.Reciprocity
open scoped NumberField BigOperators Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

theorem finitePlaceHilbertSymbol_exponent_compatibility (m n : ℕ+)
    (hmuM : (primitiveRoots (m : ℕ) K).Nonempty)
    (hmuN : (primitiveRoots (n : ℕ) K).Nonempty) (hmn : (m : ℕ) ∣ (n : ℕ))
    (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ) :
    (finitePlaceHilbertSymbol K m (Nat.cast_ne_zero.mpr m.ne_zero) hmuM v a b).val =
      (finitePlaceHilbertSymbol K n (Nat.cast_ne_zero.mpr n.ne_zero) hmuN v a b).val ^
        ((n : ℕ) / (m : ℕ)) := by
  let C := (HeightOneSpectrum.adicAbv K v).Completion
  let : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField C := finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let hmC := finitePlaceHilbert_natCast_ne_zero K m (Nat.cast_ne_zero.mpr m.ne_zero) v
  let hnC := finitePlaceHilbert_natCast_ne_zero K n (Nat.cast_ne_zero.mpr n.ne_zero) v
  let hmuMC := finitePlaceHilbert_primitiveRoots_nonempty K m hmuM v
  let hmuNC := finitePlaceHilbert_primitiveRoots_nonempty K n hmuN v
  have hm := congrArg Subtype.val (finitePlaceHilbertSymbol_map_eq_localHilbertSymbol
    K m (Nat.cast_ne_zero.mpr m.ne_zero) hmuM v a b)
  have hn := congrArg Subtype.val (finitePlaceHilbertSymbol_map_eq_localHilbertSymbol
    K n (Nat.cast_ne_zero.mpr n.ne_zero) hmuN v a b)
  change Units.map (algebraMap K C).toMonoidHom
      (finitePlaceHilbertSymbol K m (Nat.cast_ne_zero.mpr m.ne_zero) hmuM v a b).val =
    (LocalClassFieldTheory.Kummer.localHilbertSymbol C m hmC hmuMC
      (finitePlaceHilbert_completionUnit K v a) (finitePlaceHilbert_completionUnit K v b)).val at hm
  change Units.map (algebraMap K C).toMonoidHom
      (finitePlaceHilbertSymbol K n (Nat.cast_ne_zero.mpr n.ne_zero) hmuN v a b).val =
    (LocalClassFieldTheory.Kummer.localHilbertSymbol C n hnC hmuNC
      (finitePlaceHilbert_completionUnit K v a) (finitePlaceHilbert_completionUnit K v b)).val at hn
  apply Units.map_injective (algebraMap K C).injective
  rw [map_pow, hm, hn]
  exact LocalClassFieldTheory.Kummer.localHilbertSymbol_exponentCompatibility
    C m n hmC hnC hmuMC hmuNC hmn _ _

theorem globalFinitePlaceHilbertSymbol_exponent_compatibility (m n : ℕ+)
    (hmuM : (primitiveRoots (m : ℕ) K).Nonempty)
    (hmuN : (primitiveRoots (n : ℕ) K).Nonempty) (hmn : (m : ℕ) ∣ (n : ℕ))
    (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ) :
    (globalFinitePlaceHilbertSymbol K m (Nat.cast_ne_zero.mpr m.ne_zero) hmuM v a b).val =
      (globalFinitePlaceHilbertSymbol K n (Nat.cast_ne_zero.mpr n.ne_zero) hmuN v a b).val ^
        ((n : ℕ) / (m : ℕ)) :=
  finitePlaceHilbertSymbol_exponent_compatibility K m n hmuM hmuN hmn v a b

theorem sLocalHilbertForm_globalMap (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a b : Kˣ) :
    sLocalHilbertForm K n hmu S (sLocalGlobalClassMap K n S a) (sLocalGlobalClassMap K n S b) =
      ∏ v : S, globalFinitePlaceHilbertSymbol K n (Nat.cast_ne_zero.mpr n.ne_zero) hmu v.1 a b := by
  rw [sLocalHilbertForm_apply]
  apply Finset.prod_congr rfl
  intro v _
  change GlobalHilbertPairingFamily.finiteFactor K (finitePlaceAdicHilbertPairingFamily K n hmu)
    hmu v.1 a b = _
  exact finitePlaceAdicHilbertPairingFamily_finiteFactor K n (Nat.cast_ne_zero.mpr n.ne_zero) hmu v.1 a b

theorem sLocalHilbertForm_global_exponent_compatibility (m n : ℕ+)
    (hmuM : (primitiveRoots (m : ℕ) K).Nonempty)
    (hmuN : (primitiveRoots (n : ℕ) K).Nonempty) (hmn : (m : ℕ) ∣ (n : ℕ))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a b : Kˣ) :
    (sLocalHilbertForm K m hmuM S (sLocalGlobalClassMap K m S a) (sLocalGlobalClassMap K m S b)).val =
      (sLocalHilbertForm K n hmuN S (sLocalGlobalClassMap K n S a)
        (sLocalGlobalClassMap K n S b)).val ^ ((n : ℕ) / (m : ℕ)) := by
  rw [sLocalHilbertForm_globalMap, sLocalHilbertForm_globalMap]
  change (rootsOfUnity (m : ℕ) K).subtype (∏ v : S,
      globalFinitePlaceHilbertSymbol K m (Nat.cast_ne_zero.mpr m.ne_zero) hmuM v.1 a b) =
    ((rootsOfUnity (n : ℕ) K).subtype (∏ v : S,
      globalFinitePlaceHilbertSymbol K n (Nat.cast_ne_zero.mpr n.ne_zero) hmuN v.1 a b)) ^ _
  rw [map_prod, map_prod, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro v _
  exact globalFinitePlaceHilbertSymbol_exponent_compatibility K m n hmuM hmuN hmn v.1 a b

theorem sLocalHilbertForm_sixth_square
    (hmu₂ : (primitiveRoots 2 K).Nonempty) (hmu₆ : (primitiveRoots 6 K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (x y : SLocalPowerClasses K 6 S) :
    (sLocalHilbertForm K 2 hmu₂ S (sLocalSixthCRT K S x).1 (sLocalSixthCRT K S y).1).val =
      (sLocalHilbertForm K 6 hmu₆ S x y).val ^ 3 := by
  obtain ⟨a, rfl⟩ := sLocalGlobalClassMap_surjective K 6 hmu₆ S x
  obtain ⟨b, rfl⟩ := sLocalGlobalClassMap_surjective K 6 hmu₆ S y
  rw [sLocalSixthCRT_globalClass, sLocalSixthCRT_globalClass]
  exact sLocalHilbertForm_global_exponent_compatibility K 2 6 hmu₂ hmu₆ (by decide) S a b

theorem sLocalHilbertForm_sixth_cube
    (hmu₃ : (primitiveRoots 3 K).Nonempty) (hmu₆ : (primitiveRoots 6 K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (x y : SLocalPowerClasses K 6 S) :
    (sLocalHilbertForm K 3 hmu₃ S (sLocalSixthCRT K S x).2 (sLocalSixthCRT K S y).2).val =
      (sLocalHilbertForm K 6 hmu₆ S x y).val ^ 2 := by
  obtain ⟨a, rfl⟩ := sLocalGlobalClassMap_surjective K 6 hmu₆ S x
  obtain ⟨b, rfl⟩ := sLocalGlobalClassMap_surjective K 6 hmu₆ S y
  rw [sLocalSixthCRT_globalClass, sLocalSixthCRT_globalClass]
  exact sLocalHilbertForm_global_exponent_compatibility K 3 6 hmu₃ hmu₆ (by decide) S a b

end
end ArtinMatthews
