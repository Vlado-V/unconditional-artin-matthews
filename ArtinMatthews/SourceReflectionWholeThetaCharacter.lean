module

public import ArtinMatthews.SourceReflectionThetaDictionary
public import ArtinMatthews.SourceComplexPlaceUnitHaar


set_option backward.privateInPublic true
@[expose] public section

/-! The actual multiplicative reflected phase on the whole S-local
group, with its original oriented archimedean factors. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open IsDedekindDomain AngularLambda AllowedGenerators SourcePhysical QuadraticWeil
open scoped NumberField Classical BigOperators

noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

def sourceReflectionArchAngularPlace (v : InfinitePlace F) : v.Completionˣ →* ℂˣ :=
  (zpowGroupHom (-sourceReflectionAngularInfinityExponent F hζ v)).comp
    ((Units.map complexAngularHom.toMonoidHom).comp
      (sourceComplexPlaceUnitsEquiv (IsTotallyComplex.isComplex v)).toMonoidHom)

theorem sourceReflectionArchAngularPlace_val (v : InfinitePlace F) (x : v.Completionˣ) :
    (sourceReflectionArchAngularPlace F hζ v x : ℂ) =
      complexAngular (ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex v) (x:v.Completion)) ^
        (-sourceReflectionAngularInfinityExponent F hζ v) := by
  change ((Units.map complexAngularHom.toMonoidHom
    (sourceComplexPlaceUnitsEquiv (IsTotallyComplex.isComplex v) x) : ℂˣ) ^
      (-sourceReflectionAngularInfinityExponent F hζ v)).val = _
  rw [Units.val_zpow_eq_zpow_val]
  rfl

theorem sourceReflectionArchAngularPlace_continuous (v : InfinitePlace F) :
    Continuous (sourceReflectionArchAngularPlace F hζ v) := by
  let e := ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex v)
  have he : Continuous (fun x : v.Completionˣ => e (x:v.Completion)) :=
    (isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex v)).continuous.comp Units.continuous_val
  have he0 (x : v.Completionˣ) : e (x:v.Completion) ≠ 0 := by
    intro h
    exact x.ne_zero (e.injective (h.trans e.map_zero.symm))
  have hc : Continuous (fun x : v.Completionˣ => complexAngular (e (x:v.Completion))) := by
    change Continuous (fun x : v.Completionˣ => e (x:v.Completion) / (‖e (x:v.Completion)‖ : ℂ))
    apply he.div (Complex.continuous_ofReal.comp he.norm)
    intro x
    exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (he0 x))
  have hn (x : v.Completionˣ) : complexAngular (e (x:v.Completion)) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [complexAngular_norm (he0 x)]
    exact one_ne_zero
  apply Units.isEmbedding_val₀.continuous_iff.mpr
  simpa only [Function.comp_def, sourceReflectionArchAngularPlace_val] using
    hc.zpow₀ (-sourceReflectionAngularInfinityExponent F hζ v) (fun x => Or.inl (hn x))

def sourceReflectionArchAngularCharacter : (∀ v : InfinitePlace F, v.Completionˣ) →* ℂˣ where
  toFun x := ∏ v : InfinitePlace F, sourceReflectionArchAngularPlace F hζ v (x v)
  map_one' := by simp
  map_mul' x y := by simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib]

theorem sourceReflectionArchAngularCharacter_val (x : ∀ v : InfinitePlace F, v.Completionˣ) :
    (sourceReflectionArchAngularCharacter F hζ x : ℂ) =
      ∏ v : InfinitePlace F,
        complexAngular (ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex v) (x v : v.Completion)) ^
          (-sourceReflectionAngularInfinityExponent F hζ v) := by
  change ((∏ v : InfinitePlace F, sourceReflectionArchAngularPlace F hζ v (x v) : ℂˣ):ℂ) = _
  simp only [Units.coe_prod, sourceReflectionArchAngularPlace_val]

theorem sourceReflectionArchAngularCharacter_continuous :
    Continuous (sourceReflectionArchAngularCharacter F hζ) := by
  change Continuous (fun x : ∀ v : InfinitePlace F, v.Completionˣ =>
    ∏ v : InfinitePlace F, sourceReflectionArchAngularPlace F hζ v (x v))
  exact continuous_finsetProd _ (fun v _ =>
    (sourceReflectionArchAngularPlace_continuous F hζ v).comp (continuous_apply v))

theorem sourceReflectionArchAngularCharacter_norm (x : ∀ v : InfinitePlace F, v.Completionˣ) :
    ‖(sourceReflectionArchAngularCharacter F hζ x : ℂ)‖ = 1 := by
  rw [sourceReflectionArchAngularCharacter_val, norm_prod]
  apply Finset.prod_eq_one
  intro v _
  rw [norm_zpow, complexAngular_norm]
  · exact one_zpow _
  · let e := ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex v)
    intro hz
    exact (x v).ne_zero (e.injective (hz.trans e.map_zero.symm))

variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "S" => sourceHilbertSet F S₀
variable {J : Ideal (𝓞 F)}

def sourceReflectionWholeThetaCharacter
    (hBad : standardWeilBadPlaces F ⊆ S) (η : EvenIdealRayCharacter F J) (hJ : J ≠ ⊥) : SWholeUnits F S →* ℂˣ :=
  (sourceReflectionLocalThetaCharacter F S₀ hJ hζ hBad η).comp (MonoidHom.snd _ _) *
    (sourceReflectionArchAngularCharacter F hζ).comp (MonoidHom.fst _ _)

theorem sourceReflectionWholeThetaCharacter_val
    (hBad : standardWeilBadPlaces F ⊆ S) (η : EvenIdealRayCharacter F J) (hJ : J ≠ ⊥) (x : SWholeUnits F S) :
    (sourceReflectionWholeThetaCharacter F hζ S₀ hBad η hJ x : ℂ) =
      (sourceReflectionLocalThetaCharacter F S₀ hJ hζ hBad η x.2 : ℂ) *
      ∏ v : InfinitePlace F,
        complexAngular (ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex v)
          (x.1 v : v.Completion)) ^ (-sourceReflectionAngularInfinityExponent F hζ v) := by
  change ((sourceReflectionLocalThetaCharacter F S₀ hJ hζ hBad η x.2 *
    sourceReflectionArchAngularCharacter F hζ x.1 : ℂˣ) : ℂ) = _
  rw [Units.val_mul, sourceReflectionArchAngularCharacter_val F hζ]

theorem sourceReflectionWholeThetaCharacter_continuous
    (hBad : standardWeilBadPlaces F ⊆ S) (η : EvenIdealRayCharacter F J) (hJ : J ≠ ⊥) :
    Continuous (sourceReflectionWholeThetaCharacter F hζ S₀ hBad η hJ) := by
  change Continuous (fun x : SWholeUnits F S =>
    sourceReflectionLocalThetaCharacter F S₀ hJ hζ hBad η x.2 *
      sourceReflectionArchAngularCharacter F hζ x.1)
  exact ((sourceReflectionLocalThetaCharacter_continuous F S₀ hJ hζ hBad η).comp
    continuous_snd).mul ((sourceReflectionArchAngularCharacter_continuous F hζ).comp continuous_fst)

theorem sourceReflectionWholeThetaCharacter_norm
    (hBad : standardWeilBadPlaces F ⊆ S) (η : EvenIdealRayCharacter F J) (hJ : J ≠ ⊥) (x : SWholeUnits F S) :
    ‖(sourceReflectionWholeThetaCharacter F hζ S₀ hBad η hJ x : ℂ)‖ = 1 := by
  change ‖((sourceReflectionLocalThetaCharacter F S₀ hJ hζ hBad η x.2 *
    sourceReflectionArchAngularCharacter F hζ x.1 : ℂˣ) : ℂ)‖ = 1
  rw [Units.val_mul, norm_mul, sourceReflectionLocalThetaCharacter_norm F S₀ hJ hζ hBad η,
    sourceReflectionArchAngularCharacter_norm F hζ, mul_one]

theorem sourceReflectionThetaValue_eq_whole
    (hBad : standardWeilBadPlaces F ⊆ S) (η : EvenIdealRayCharacter F J) (hJ : J ≠ ⊥)
    (hcut : principalAngularCutoff F J ⊆ S) (e : SourcePrimeExponents F S₀) :
    reflectionThetaValue F hζ S₀ hBad η e =
      (sourceReflectionWholeThetaCharacter F hζ S₀ hBad η hJ
        (sWholeDiagonal F S (sourcePrimeExponentUnit F hζ S₀ e)) : ℂ) := by
  let a := sourcePrimeExponentUnit F hζ S₀ e
  have h := sourceReflectionThetaValue_eq_local_mul_arch F hζ S₀ hBad η hJ hcut e
  change reflectionThetaValue F hζ S₀ hBad η e = _ at h
  rw [h, sourceReflectionWholeThetaCharacter_val F hζ S₀ hBad η hJ]
  change (_ : ℂ) * (∏ v : InfinitePlace F, complexAngular (v.embedding (a:F)) ^
    (-sourceReflectionAngularInfinityExponent F hζ v)) = _ * _
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  apply congrArg (fun z : ℂ => complexAngular z ^ (-sourceReflectionAngularInfinityExponent F hζ v))
  rw [ringEquivComplexOfIsComplex_apply]
  change v.embedding (a:F) =
    extensionEmbedding v (((WithAbs.equiv v.1).symm (a:F) : WithAbs v.1) : v.Completion)
  rw [extensionEmbedding_coe, RingEquiv.apply_symm_apply]

theorem sourceReflectionThetaValue_div_phase
    (hBad : standardWeilBadPlaces F ⊆ S) (η : EvenIdealRayCharacter F J) (hJ : J ≠ ⊥)
    (hcut : principalAngularCutoff F J ⊆ S) (e : SourcePrimeExponents F S₀)
    (x : SWholeUnits F S) :
    reflectionThetaValue F hζ S₀ hBad η e /
      (sourceReflectionWholeThetaCharacter F hζ S₀ hBad η hJ x : ℂ) =
    (sourceReflectionWholeThetaCharacter F hζ S₀ hBad η hJ
      (sWholeDiagonal F S (sourcePrimeExponentUnit F hζ S₀ e) / x) : ℂ) := by
  rw [sourceReflectionThetaValue_eq_whole F hζ S₀ hBad η hJ hcut e, map_div,
    Units.val_div_eq_div_val]

end
end ArtinMatthews.VaryingKummerAnalytic
