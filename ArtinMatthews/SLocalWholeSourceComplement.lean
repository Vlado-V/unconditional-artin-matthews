module

public import ArtinMatthews.SLocalWholePowerClasses
public import ArtinMatthews.SLocalSixthOrthogonal


set_option backward.privateInPublic true
@[expose] public section

/-! The actual source space F_S^x/(F_S^x)^6, with the literal diagonal
S-unit image, has a constructed isotropic complement. Infinite local
factors are included in the space and their power classes are proved
trivial. Injection and E-perpendicular=E are conclusions. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain KummerTheory
open GlobalClassFieldTheory.GlobalClassFields
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

def sWholeUnitPowerClassMap (n : ℕ+) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (SUnitGroup (K := K) S ⧸
      (powMonoidHom (n : ℕ) : SUnitGroup (K := K) S →* SUnitGroup (K := K) S).range) →*
      SWholePowerClasses K n S :=
  QuotientGroup.lift (M := SWholePowerClasses K n S) _
    ((sWholeGlobalClassMap K n S).comp (SUnitGroup (K := K) S).subtype) (by
      rintro _ ⟨u, rfl⟩
      change ((sWholeGlobalClassMap K n S).comp (SUnitGroup (K := K) S).subtype)
        (u ^ (n : ℕ)) = 1
      rw [map_pow]
      exact powerQuotient_pow_eq_one (n : ℕ) _)

section TotallyComplex
variable [NumberField.IsTotallyComplex K]

@[simp] theorem sWholePowerEquiv_unitPowerClassMap (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (q : SUnitGroup (K := K) S ⧸
      (powMonoidHom (n : ℕ) : SUnitGroup (K := K) S →* SUnitGroup (K := K) S).range) :
    sWholePowerEquiv K n S (sWholeUnitPowerClassMap K n S q) = sUnitPowerClassMap K n S q := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective _ q
  change sWholePowerEquiv K n S (sWholeGlobalClassMap K n S (u : Kˣ)) = _
  rw [sWholePowerEquiv_globalClass, sLocalGlobalClassMap_sUnit]
  rfl

theorem sWholeUnitPowerClassMap_injective (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : sUnitKummerNormSupport (K := K) n ∅ ⊆ S) :
    Function.Injective (sWholeUnitPowerClassMap K n S) := by
  intro q r hqr
  apply sUnitPowerClassMap_injective K n hmu S hS
  have h := congrArg (sWholePowerEquiv K n S) hqr
  simpa only [sWholePowerEquiv_unitPowerClassMap] using h

end TotallyComplex

def sourceWholeHilbertForm {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    SWholePowerClasses K 6 S →* (SWholePowerClasses K 6 S →* rootsOfUnity 6 K) := by
  let : NumberField.IsTotallyComplex K := source_isTotallyComplex K hζ
  exact sWholeHilbertForm K 6 (sLocalPrimitiveRoots K 6 (sourceHilbertRootSix_isPrimitive K hζ)) S

theorem source_sixth_whole_isotropic_complement {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ B : Subgroup (SWholePowerClasses K 6 (sourceHilbertSet K S₀)),
      IsCompl (sWholeUnitPowerImage K 6 (sourceHilbertSet K S₀)) B ∧
      ∀ x ∈ B, ∀ y ∈ B, sourceWholeHilbertForm K hζ (sourceHilbertSet K S₀) x y = 1 := by
  let : NumberField.IsTotallyComplex K := source_isTotallyComplex K hζ
  obtain ⟨B, hC, hI⟩ := source_sixth_isotropic_complement K hζ S₀
  let e := sWholePowerEquiv K 6 (sourceHilbertSet K S₀)
  have he : (sUnitPowerImage K 6 (sourceHilbertSet K S₀)).comap e.toMonoidHom =
      sWholeUnitPowerImage K 6 (sourceHilbertSet K S₀) := by
    ext x
    exact (sWholePowerEquiv_unitImage_iff K 6 (sourceHilbertSet K S₀) x).symm
  have h := e.comapSubgroup.isCompl hC
  change IsCompl ((sUnitPowerImage K 6 (sourceHilbertSet K S₀)).comap e.toMonoidHom)
    (B.comap e.toMonoidHom) at h
  rw [he] at h
  refine ⟨B.comap e.toMonoidHom, h, ?_⟩
  intro x hx y hy
  exact hI (e x) hx (e y) hy

theorem source_sixth_whole_unitImage_selfOrthogonal {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∀ x : SWholePowerClasses K 6 (sourceHilbertSet K S₀),
      (∀ y ∈ sWholeUnitPowerImage K 6 (sourceHilbertSet K S₀),
        sourceWholeHilbertForm K hζ (sourceHilbertSet K S₀) x y = 1) ↔
      x ∈ sWholeUnitPowerImage K 6 (sourceHilbertSet K S₀) := by
  let : NumberField.IsTotallyComplex K := source_isTotallyComplex K hζ
  let e := sWholePowerEquiv K 6 (sourceHilbertSet K S₀)
  intro x
  rw [sWholePowerEquiv_unitImage_iff]
  rw [← source_sixth_unitImage_selfOrthogonal K hζ S₀]
  constructor
  · intro hx y hy
    have hy' : e.symm y ∈ sWholeUnitPowerImage K 6 (sourceHilbertSet K S₀) := by
      rw [sWholePowerEquiv_unitImage_iff]
      simpa only [e, MulEquiv.apply_symm_apply] using hy
    have h := hx (e.symm y) hy'
    change sLocalHilbertForm K 6
      (sLocalPrimitiveRoots K 6 (sourceHilbertRootSix_isPrimitive K hζ))
      (sourceHilbertSet K S₀) (e x) (e (e.symm y)) = 1 at h
    simpa only [e.apply_symm_apply] using h
  · intro hx y hy
    exact hx (e y) ((sWholePowerEquiv_unitImage_iff K 6 (sourceHilbertSet K S₀) y).mp hy)

theorem source_sixth_whole_unitPowerClassMap_injective {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Injective (sWholeUnitPowerClassMap K 6 (sourceHilbertSet K S₀)) := by
  let : NumberField.IsTotallyComplex K := source_isTotallyComplex K hζ
  exact sWholeUnitPowerClassMap_injective K 6
    (sLocalPrimitiveRoots K 6 (sourceHilbertRootSix_isPrimitive K hζ)) _
    (normSupport_subset_sourceHilbertSet K S₀ 6 (Or.inr (Or.inr rfl)))

end
end ArtinMatthews
