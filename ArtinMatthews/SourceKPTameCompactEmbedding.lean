module

public import ArtinMatthews.SourceKPDeepAdelicEmbedding
public import ArtinMatthews.SourceKPAdelicCompactSection
public import ArtinMatthews.SourceKPLocalBorelEmbedding


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine tame compact section maps to the prescribed global
compact subgroup because the inverse local cochain cancels exactly. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K)) (h6 : (6 : 𝓞 K) ∉ P.asIdeal)

def sourceKPTameAdelicMatrix (g : SourceFiniteKP2Integral K P) : sourceKPAdelicDeepCompactMatrix K hζ :=
  ⟨sourceKPFullSingleMatrix K P g.val, by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro Q
      by_cases hQP : Q = P
      · subst Q
        rw [sourceKPFullSingleMatrix_same]
        exact g.property
      · rw [sourceKPFullSingleMatrix_other K P Q hQP]
        exact sourceKPIntegralMatrix_one _
    · intro w
      rw [sourceKPFullSingleMatrix_complex]
      exact sourceArchUnitaryGL.range.one_mem
    · intro Q hQ
      have hQP : Q ≠ P := by
        intro he
        subst Q
        exact h6 hQ
      rw [sourceKPFullSingleMatrix_other K P Q hQP]
      exact (sourceKPDeepLocalBase K Q).range.one_mem⟩

theorem sourceKPTameAdelicMatrix_lift (g : SourceFiniteKP2Integral K P) :
    sourceKPAdelicDeepCompactLift K hζ (sourceKPTameAdelicMatrix K hζ P h6 g) =
      sourceKPAdelicLocalProjective K hζ P (sourceFiniteKP2ProjectiveCompactSection K hζ P h6 g) := by
  change (ProjGenLinGroup.mk (sourceKPGL2ProductEquiv K
      (sourceKPFullSingleMatrix K P g.val)).1,
    sourceKPFiniteAdeleProjectiveLift K hζ (sourceKPGL2ProductEquiv K
      (sourceKPFullSingleMatrix K P g.val)).2) = _
  rw [sourceKPFullSingleMatrix_components]
  apply Prod.ext
  · exact map_one _
  · change sourceKPFiniteAdeleProjectiveMk K hζ ⟨1, sourceKPAdeleSingleMatrix K P g.val⟩ =
      sourceKPFiniteAdeleProjectiveMk K hζ
        (sourceKPAdeleLocalCover K hζ P (sourceFiniteKP2CompactSection K hζ P h6 g))
    apply congrArg (sourceKPFiniteAdeleProjectiveMk K hζ)
    apply SourceKPFiniteAdeleCover.ext
    · change 1 = (sourceKPRootsTransport K hζ P).symm
        (sourceKPCompactPhase (sourceKPFiniteVal K P) (sourceFiniteKPHilbert K hζ P) g.val /
          sourceKPFinitePhase K hζ P g.val)
      rw [sourceKPFinitePhase, ite_eq_left h6, div_self', map_one]
    · rfl

theorem sourceKPTameAdelicMatrix_mem (g : SourceFiniteKP2Integral K P) :
    sourceKPAdelicLocalProjective K hζ P (sourceFiniteKP2ProjectiveCompactSection K hζ P h6 g) ∈
      sourceKPAdelicDeepCompact K hζ :=
  ⟨sourceKPTameAdelicMatrix K hζ P h6 g, sourceKPTameAdelicMatrix_lift K hζ P h6 g⟩

theorem sourceKPAdelicCompactSection_right_local (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (k : SourceFiniteKP2Integral K P) :
    (sourceKPAdelicCompactSection K hζ s).val
      (g * sourceKPAdelicLocalProjective K hζ P (sourceFiniteKP2ProjectiveCompactSection K hζ P h6 k)) =
      (sourceKPAdelicCompactSection K hζ s).val g := by
  let k' : sourceKPAdelicDeepCompact K hζ :=
    ⟨sourceKPAdelicLocalProjective K hζ P (sourceFiniteKP2ProjectiveCompactSection K hζ P h6 k),
      sourceKPTameAdelicMatrix_mem K hζ P h6 k⟩
  exact congrArg (fun f : SourceKPAdelicPrincipalSeries K hζ s => f.val g)
    (sourceKPAdelicCompactSection_right K hζ s k')

theorem sourceKPAdelicCompactSection_local_factor (s : ℂ)
    (g : SourceFiniteKP2Projective K hζ P) (b : SourceFiniteKPProjectiveBorel K hζ P)
    (k : SourceFiniteKP2Integral K P)
    (hg : g = b.val * sourceFiniteKP2ProjectiveCompactSection K hζ P h6 k) :
    (sourceKPAdelicCompactSection K hζ s).val (sourceKPAdelicLocalProjective K hζ P g) =
      sourceKPAdelicLocalBorelRepresentation K hζ P s b (sourceKPAdelicUnitSphericalVector K hζ s) := by
  let k' : sourceKPAdelicDeepCompact K hζ :=
    ⟨sourceKPAdelicLocalProjective K hζ P (sourceFiniteKP2ProjectiveCompactSection K hζ P h6 k),
      sourceKPTameAdelicMatrix_mem K hζ P h6 k⟩
  apply sourceKPAdelicCompactSection_factor K hζ s _ (sourceKPAdelicLocalBorel K hζ P b) k'
  rw [hg, map_mul]
  rfl

end
end ArtinMatthews
