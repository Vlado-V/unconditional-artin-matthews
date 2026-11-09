module

public import ArtinMatthews.SourceArchCompletedJacquet
public import ArtinMatthews.SourceArchBorelInduction
public import ArtinMatthews.SourceArchCompactUnitary
public import ArtinMatthews.SourceArchAdelicEmbedding
public import ArtinMatthews.SourceSLocalOtherTensor


set_option backward.privateInPublic true
@[expose] public section

/-! The nonzero actual archimedean Jacquet vector and its injection
into the existing adelic projective group. -/
namespace ArtinMatthews.SourceArchJacquet

open NumberField NumberField.InfinitePlace Matrix
open ArtinMatthews.SourceReflection
open scoped MatrixGroups
noncomputable section

theorem sourceArchBorel_eq_map :
    sourceArchBorel = (sourceGL2NormalizedBorel ℂ).map ProjGenLinGroup.mk := by
  ext g
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b.val, b.property, hb⟩
  · rintro ⟨b, hb, he⟩
    exact ⟨⟨b, hb⟩, he⟩

theorem sourceArchSphericalWhittaker_ne_zero (y : ℂˣ) :
    sourceArchSphericalWhittaker y ≠ 0 := by
  intro h
  have hp := sourceThetaBesselProfile_pos
    (by positivity : 0 < 4 * Real.pi) (sq_pos_of_pos (norm_pos_iff.mpr y.ne_zero))
  rw [sourceThetaBesselProfile_eq_weightedWhittaker, h, mul_zero, zero_div, Complex.zero_re] at hp
  exact lt_irrefl _ hp

variable (F : Type) [Field F] [NumberField F]

def sourceArchComplexToAdelic {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (v : InfinitePlace F) (hv : IsComplex v) : PGL(2, ℂ) →* SourceKPAdelicProjective F hζ :=
  (sourceArchLocalToAdelic F hζ v).comp
    (ProjGenLinGroup.map (sourceArchCompletionEquiv F v hv).symm.toRingHom)

theorem sourceArchComplexToAdelic_injective {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (v : InfinitePlace F) (hv : IsComplex v) :
    Function.Injective (sourceArchComplexToAdelic F hζ v hv) := by
  apply (sourceArchLocalToAdelic_injective F hζ v).comp
  apply Function.LeftInverse.injective
    (g := ProjGenLinGroup.map (sourceArchCompletionEquiv F v hv).toRingHom)
  intro g
  rw [← MonoidHom.comp_apply, ← ProjGenLinGroup.map_comp,
    RingEquiv.toRingHom_comp_symm_toRingHom, ProjGenLinGroup.map_id]
  rfl

theorem sourceArchCompletedWhittaker_ne_zero (v : InfinitePlace F) (hv : IsComplex v)
    (y : v.Completionˣ) : sourceArchCompletedWhittaker F v hv y ≠ 0 := by
  rw [sourceArchCompletedWhittaker_eq]
  exact sourceArchSphericalWhittaker_ne_zero _

theorem sourceArchCompletedWhittaker_sourceNorm (v : InfinitePlace F) (hv : IsComplex v)
    (y : v.Completionˣ) :
    sourceThetaBesselProfile (4 * Real.pi) (SourcePhysical.sourceSheetArchNorm v y) =
      (Real.sqrt (SourcePhysical.sourceSheetArchNorm v y) : ℂ) *
        sourceArchCompletedWhittaker F v hv y / (sourceArchJacquetConstant : ℂ) :=
  sourceArchCompletedWhittaker_sourceProfile F v hv y

end
end ArtinMatthews.SourceArchJacquet
