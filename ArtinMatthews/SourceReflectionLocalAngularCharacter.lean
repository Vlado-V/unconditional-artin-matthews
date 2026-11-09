module

public import ArtinMatthews.SourceReflectionAngularPrincipal


set_option backward.privateInPublic true
@[expose] public section

/-! The angular correction descends to the fixed retained local units
by the actual multiplicative weak approximation theorem. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain RayClass SourcePhysical
open scoped NumberField Classical

noncomputable section

private def liftAlongSurjection {A B C : Type*} [MulOneClass A] [MulOneClass B] [MulOneClass C]
    (δ : A →* B) (hδ : Function.Surjective δ) (f : A →* C)
    (h : ∀ a b, δ a = δ b → f a = f b) : B →* C := by
  let r := hδ.hasRightInverse.choose
  have hr : Function.RightInverse r δ := hδ.hasRightInverse.choose_spec
  refine { toFun := f ∘ r, map_one' := ?_, map_mul' := ?_ }
  · change f (r 1) = 1
    rw [h (r 1) 1 ((hr 1).trans (map_one δ).symm), map_one]
  · intro x y
    change f (r (x * y)) = f (r x) * f (r y)
    rw [h (r (x * y)) (r x * r y) (by rw [hr, map_mul, hr, hr]), map_mul]

private theorem liftAlongSurjection_apply {A B C : Type*} [MulOneClass A] [MulOneClass B] [MulOneClass C]
    (δ : A →* B) (hδ : Function.Surjective δ) (f : A →* C)
    (h : ∀ a b, δ a = δ b → f a = f b) (a : A) :
    liftAlongSurjection δ hδ f h (δ a) = f a :=
  h _ _ (hδ.hasRightInverse.choose_spec (δ a))

variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

local notation "S" => sourceHilbertSet F S₀
local notation "M" => sourceReflectionAngularModulus F S₀
local notation "hM" => sourceReflectionAngularModulus_ne_bot F S₀
local notation "n" => integralIdealFiniteModulus M hM
local notation "U" => (fun P : S => localHigherUnitGroup (Subtype.val P) (n (Subtype.val P)))
local notation "d" => IdeleGroup.principalLocalQuotientMap S U

def sourceReflectionAngularFieldCorrection : Fˣ →* ℂˣ :=
  sourceReflectionAngularField F hζ /
    ((sourceReflectionAngularIdealHom F hζ S₀).comp
      ((IdeleGroup.fractionalIdeal (K := F)).comp (sourceReflectionExteriorIdele F S)))

private def angularLocalQuotient :
    SFiniteUnits F S →* (∀ P : S, (P.val.adicCompletion F)ˣ ⧸ U P) :=
  MonoidHom.pi fun P => (QuotientGroup.mk' (U P)).comp (Pi.evalMonoidHom _ P)

private theorem angularLocalQuotient_eq_one (u : SFiniteUnits F S) :
    angularLocalQuotient F S₀ u = 1 ↔ u ∈ sourceReflectionDeepUnits F S n := by
  rw [sourceReflectionDeepUnits_mem_iff]
  constructor
  · intro h P
    exact (QuotientGroup.eq_one_iff _).mp (congrFun h P)
  · intro h
    funext P
    exact (QuotientGroup.eq_one_iff _).mpr (h P)

private theorem angularPrincipalQuotient_surjective : Function.Surjective d :=
  IdeleGroup.principalLocalQuotientMap_surjective S U
    (fun P => isOpen_localHigherUnitGroup P.val (n P.val))

private theorem angularFieldCorrection_eq_one (a : Fˣ) (ha : d a = 1) :
    sourceReflectionAngularFieldCorrection F hζ S₀ a = 1 := by
  have hq : angularLocalQuotient F S₀ (sourceReflectionFiniteDiagonal F S a) = 1 := ha
  have hu := (angularLocalQuotient_eq_one F S₀ _).mp hq
  have h := sourceReflectionAngularIdealHom_exterior_eq_field_of_deep F hζ S₀ a hu
  change sourceReflectionAngularField F hζ a /
    sourceReflectionAngularIdealHom F hζ S₀
      (IdeleGroup.fractionalIdeal (sourceReflectionExteriorIdele F S a)) = 1
  rw [h, div_self']

private theorem angularFieldCorrection_congr (a b : Fˣ) (hab : d a = d b) :
    sourceReflectionAngularFieldCorrection F hζ S₀ a =
      sourceReflectionAngularFieldCorrection F hζ S₀ b := by
  have hd : d (a / b) = 1 := by
    rw [map_div, hab]
    funext P
    change (d b P) / (d b P) = 1
    exact div_self' (d b P)
  have h := angularFieldCorrection_eq_one F hζ S₀ (a / b) hd
  rwa [map_div, div_eq_one] at h

private def angularLocalQuotientCharacter :
    (∀ P : S, (P.val.adicCompletion F)ˣ ⧸ U P) →* ℂˣ :=
  liftAlongSurjection d (angularPrincipalQuotient_surjective F S₀)
    (sourceReflectionAngularFieldCorrection F hζ S₀) (angularFieldCorrection_congr F hζ S₀)

def sourceReflectionLocalAngularCharacter : SFiniteUnits F S →* ℂˣ :=
  (angularLocalQuotientCharacter F hζ S₀).comp (angularLocalQuotient F S₀)

theorem sourceReflectionLocalAngularCharacter_diagonal (a : Fˣ) :
    sourceReflectionLocalAngularCharacter F hζ S₀ (sourceReflectionFiniteDiagonal F S a) =
      sourceReflectionAngularFieldCorrection F hζ S₀ a := by
  change angularLocalQuotientCharacter F hζ S₀ (d a) = _
  unfold angularLocalQuotientCharacter
  apply liftAlongSurjection_apply

theorem sourceReflectionLocalAngularCharacter_deep (u : SFiniteUnits F S)
    (hu : u ∈ sourceReflectionDeepUnits F S n) :
    sourceReflectionLocalAngularCharacter F hζ S₀ u = 1 := by
  have hq := (angularLocalQuotient_eq_one F S₀ u).mpr hu
  simp only [sourceReflectionLocalAngularCharacter, MonoidHom.comp_apply, hq, map_one]

theorem sourceReflectionLocalAngularCharacter_continuous :
    Continuous (sourceReflectionLocalAngularCharacter F hζ S₀) :=
  sourceReflectionCharacter_continuous_of_deep F S n _
    (sourceReflectionLocalAngularCharacter_deep F hζ S₀)

theorem sourceReflectionLocalAngularCharacter_norm (u : SFiniteUnits F S) :
    ‖(sourceReflectionLocalAngularCharacter F hζ S₀ u : ℂ)‖ = 1 := by
  obtain ⟨a,ha⟩ := angularPrincipalQuotient_surjective F S₀ (angularLocalQuotient F S₀ u)
  have hq : angularLocalQuotient F S₀ u =
      angularLocalQuotient F S₀ (sourceReflectionFiniteDiagonal F S a) := ha.symm
  have he : sourceReflectionLocalAngularCharacter F hζ S₀ u =
      sourceReflectionLocalAngularCharacter F hζ S₀ (sourceReflectionFiniteDiagonal F S a) :=
    congrArg (angularLocalQuotientCharacter F hζ S₀) hq
  rw [he, sourceReflectionLocalAngularCharacter_diagonal, sourceReflectionAngularFieldCorrection,
    MonoidHom.div_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, Units.val_div_eq_div_val,
    norm_div, sourceReflectionAngularField_norm, sourceReflectionAngularIdealHom_norm, div_one]

end
end ArtinMatthews.VaryingKummerAnalytic
