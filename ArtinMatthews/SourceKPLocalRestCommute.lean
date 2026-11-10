module

public import ArtinMatthews.SourceKPAdeleLocalEmbedding
import ArtinMatthews.SourceAdelicIwasawaAssembly


set_option backward.privateInPublic true
@[expose] public section

/-! A global cover element whose projective component is trivial at P
commutes with the actual local cover at P. The compact cochain remains
in both products and cancels by the proved scalar commutation law. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

def sourceKPAdelicLocalBase : SourceKPAdelicProjective K hζ →* PGL(2, P.adicCompletion K) :=
  (ProjGenLinGroup.map (sourceKPAdeleEval K P)).comp
    ((sourceKPFiniteAdeleProjectiveProjection K hζ).comp
      (MonoidHom.snd _ _))

theorem sourceKPAdeleSingleMatrix_commute_of_scalar_at
    (g : GL (Fin 2) (P.adicCompletion K)) (h : GL (Fin 2) 𝔸ᶠ[K])
    (u : (P.adicCompletion K)ˣ)
    (hu : sourceKPAdeleMatrixAt K P h = GeneralLinearGroup.scalar (Fin 2) u) :
    Commute (sourceKPAdeleSingleMatrix K P g) h := by
  apply sourceKPAdeleMatrixAt_ext K
  intro Q
  simp only [map_mul]
  by_cases hQP : Q = P
  · subst Q
    rw [sourceKPAdeleSingleMatrix_same, hu]
    exact (GeneralLinearGroup.scalar_commute u g).symm
  · rw [sourceKPAdeleSingleMatrix_other K P Q hQP, one_mul, mul_one]

theorem sourceKPAdeleMultiplier_single_commute_of_scalar_at
    (g : GL (Fin 2) (P.adicCompletion K)) (h : GL (Fin 2) 𝔸ᶠ[K])
    (u : (P.adicCompletion K)ˣ)
    (hu : sourceKPAdeleMatrixAt K P h = GeneralLinearGroup.scalar (Fin 2) u) :
    sourceKPAdeleMultiplier K hζ (sourceKPAdeleSingleMatrix K P g) h =
      sourceKPAdeleMultiplier K hζ h (sourceKPAdeleSingleMatrix K P g) := by
  unfold sourceKPAdeleMultiplier
  apply finprod_congr
  intro Q
  unfold sourceKPAdeleLocalMultiplier
  by_cases hQP : Q = P
  · subst Q
    rw [sourceKPAdeleSingleMatrix_same, hu,
      sourceKPFiniteTwistedMultiplier_scalar_comm]
  · rw [sourceKPAdeleSingleMatrix_other K P Q hQP,
      sourceKPFiniteTwistedMultiplier_one_left, sourceKPFiniteTwistedMultiplier_one_right]

theorem sourceKPAdeleLocalCover_commute_of_scalar_at
    (g : SourceFiniteKP2Cover K hζ P) (h : SourceKPFiniteAdeleCover K hζ)
    (u : (P.adicCompletion K)ˣ)
    (hu : sourceKPAdeleMatrixAt K P h.base = GeneralLinearGroup.scalar (Fin 2) u) :
    Commute (sourceKPAdeleLocalCover K hζ P g) h := by
  apply SourceKPFiniteAdeleCover.ext
  · change _ * _ * sourceKPAdeleMultiplier K hζ (sourceKPAdeleSingleMatrix K P g.base) h.base =
      _ * _ * sourceKPAdeleMultiplier K hζ h.base (sourceKPAdeleSingleMatrix K P g.base)
    rw [sourceKPAdeleMultiplier_single_commute_of_scalar_at K hζ P g.base h.base u hu]
    ac_rfl
  · exact (sourceKPAdeleSingleMatrix_commute_of_scalar_at K P g.base h.base u hu).eq

theorem sourceKPAdelicLocalProjective_commute_of_base_one
    (g : SourceFiniteKP2Projective K hζ P) (h : SourceKPAdelicProjective K hζ)
    (hh : sourceKPAdelicLocalBase K hζ P h = 1) :
    Commute (sourceKPAdelicLocalProjective K hζ P g) h := by
  obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective (sourceFiniteKP2Scalar K hζ P).range g
  obtain ⟨h', hh'⟩ := QuotientGroup.mk'_surjective (sourceKPFiniteAdeleScalar K hζ).range h.2
  have hlocal : ProjGenLinGroup.mk (sourceKPAdeleMatrixAt K P h'.base) = 1 := by
    change ProjGenLinGroup.map (sourceKPAdeleEval K P)
      (sourceKPFiniteAdeleProjectiveProjection K hζ h.2) = 1 at hh
    rw [← hh'] at hh
    exact hh
  have hs := ProjGenLinGroup.mk_eq_one.mp hlocal
  rw [GeneralLinearGroup.center_eq_range_scalar] at hs
  obtain ⟨u, hu⟩ := hs
  apply Prod.ext
  · change 1 * h.1 = h.1 * 1
    rw [one_mul, mul_one]
  · change sourceKPFiniteAdeleProjectiveMk K hζ (sourceKPAdeleLocalCover K hζ P g') * h.2 =
      h.2 * sourceKPFiniteAdeleProjectiveMk K hζ (sourceKPAdeleLocalCover K hζ P g')
    rw [← hh']
    exact congrArg (sourceKPFiniteAdeleProjectiveMk K hζ)
      (sourceKPAdeleLocalCover_commute_of_scalar_at K hζ P g' h' u hu.symm).eq

end
end ArtinMatthews
