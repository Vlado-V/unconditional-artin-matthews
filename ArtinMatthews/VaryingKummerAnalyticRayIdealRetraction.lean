module

public import ArtinMatthews.VaryingKummerAnalyticRayPrimitivePresentation


set_option backward.privateInPublic true
@[expose] public section

/-! A canonical prime-to-conductor part of every nonzero fractional ideal.
This removes exactly the prime factors in the modulus and permits genuine
ray-class characters to be used on the full fractional-ideal group. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField RayClass IsDedekindDomain FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

def rayPrimeToIdealPart (m : Modulus K) (I : FractionalIdealGroup K) : FractionalIdealGroup K :=
  FractionalIdealGroup.factorization (Multiplicative.ofAdd
    ((FractionalIdealGroup.countVector I).filter (fun v => v ∉ m.finitePart.support)))

theorem rayPrimeToIdealPart_count (m : Modulus K) (I : FractionalIdealGroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v (rayPrimeToIdealPart m I : FractionalIdeal (𝓞 K)⁰ K) =
      if v ∈ m.finitePart.support then 0 else FractionalIdeal.count K v (I:FractionalIdeal (𝓞 K)⁰ K) := by
  rw [rayPrimeToIdealPart,FractionalIdealGroup.count_factorization]
  change (FractionalIdealGroup.countVector I).filter (fun w => w ∉ m.finitePart.support) v = _
  simp only [Finsupp.filter_apply,FractionalIdealGroup.countVector_apply,ite_not]

def rayPrimeToIdealRetraction (m : Modulus K) : FractionalIdealGroup K →* primeToModulusIdeals m where
  toFun I := ⟨rayPrimeToIdealPart m I,fun v hv => by rw [rayPrimeToIdealPart_count,ite_eq_left hv]⟩
  map_one' := by
    apply Subtype.ext
    apply FractionalIdealGroup.ext_count
    intro v
    change FractionalIdeal.count K v (rayPrimeToIdealPart m 1 : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.count K v (1 : FractionalIdeal (𝓞 K)⁰ K)
    rw [rayPrimeToIdealPart_count]
    simp only [Units.val_one,FractionalIdeal.count_one,ite_self]
  map_mul' I J := by
    apply Subtype.ext
    apply FractionalIdealGroup.ext_count
    intro v
    change FractionalIdeal.count K v (rayPrimeToIdealPart m (I*J) : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.count K v ((rayPrimeToIdealPart m I * rayPrimeToIdealPart m J : FractionalIdealGroup K) : FractionalIdeal (𝓞 K)⁰ K)
    rw [Units.val_mul,FractionalIdeal.count_mul K v (Units.ne_zero _) (Units.ne_zero _),
      rayPrimeToIdealPart_count,rayPrimeToIdealPart_count,rayPrimeToIdealPart_count,
      Units.val_mul,FractionalIdeal.count_mul K v (Units.ne_zero I) (Units.ne_zero J)]
    split_ifs <;> simp

theorem rayPrimeToIdealRetraction_coe (m : Modulus K) (I : primeToModulusIdeals m) :
    rayPrimeToIdealRetraction m (I:FractionalIdealGroup K) = I := by
  apply Subtype.ext
  apply FractionalIdealGroup.ext_count
  intro v
  change FractionalIdeal.count K v (rayPrimeToIdealPart m I : FractionalIdeal (𝓞 K)⁰ K) = _
  rw [rayPrimeToIdealPart_count]
  by_cases hv : v ∈ m.finitePart.support
  · rw [ite_eq_left hv,I.property v hv]
  · rw [ite_eq_right hv]

def idealRayCharacterExtension (m : Modulus K) (χ : IdealRayClassGroup m →* ℂˣ) :
    FractionalIdealGroup K →* ℂˣ :=
  χ.comp ((QuotientGroup.mk' (principalRayIdealSubgroup m)).comp (rayPrimeToIdealRetraction m))

theorem idealRayCharacterExtension_primeTo (m : Modulus K) (χ : IdealRayClassGroup m →* ℂˣ)
    (I : primeToModulusIdeals m) :
    idealRayCharacterExtension m χ (I:FractionalIdealGroup K) =
      χ (QuotientGroup.mk' (principalRayIdealSubgroup m) I) := by
  simp only [idealRayCharacterExtension,MonoidHom.comp_apply,rayPrimeToIdealRetraction_coe]

theorem idealRayCharacterExtension_finiteOrder (m : Modulus K) (χ : IdealRayClassGroup m →* ℂˣ)
    (hχ : ∃ e : ℕ, 0 < e ∧ ∀ c, χ c ^ e = 1) :
    ∃ e : ℕ, 0 < e ∧ ∀ I, idealRayCharacterExtension m χ I ^ e = 1 := by
  obtain ⟨e,he,h⟩ := hχ
  exact ⟨e,he,fun I => h _⟩

end
end ArtinMatthews.VaryingKummerAnalytic
