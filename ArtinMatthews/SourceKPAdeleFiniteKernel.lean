module

public import ArtinMatthews.SourceKPAdeleLocalEmbedding


set_option backward.privateInPublic true
@[expose] public section

/-! The kernel of the finite local-to-adelic product consists exactly
of central tuples with total cubic phase one. This is the central
compatibility required by the genuine exterior tensor. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicProjectiveAt (P : HeightOneSpectrum (𝓞 K)) :
    SourceKPAdelicProjective K hζ →* PGL(2, P.adicCompletion K) :=
  (ProjGenLinGroup.map (sourceKPAdeleEval K P)).comp
    ((sourceKPFiniteAdeleProjectiveProjection K hζ).comp (MonoidHom.snd _ _))

theorem sourceKPAdelicProjectiveAt_local_same (P : HeightOneSpectrum (𝓞 K))
    (g : SourceFiniteKP2Projective K hζ P) :
    sourceKPAdelicProjectiveAt K hζ P (sourceKPAdelicLocalProjective K hζ P g) =
      sourceFiniteKP2ProjectiveProjection K hζ P g := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (sourceFiniteKP2Scalar K hζ P).range g
  change ProjGenLinGroup.mk (sourceKPAdeleMatrixAt K P (sourceKPAdeleSingleMatrix K P x.base)) =
    ProjGenLinGroup.mk x.base
  rw [sourceKPAdeleSingleMatrix_same]

theorem sourceKPAdelicProjectiveAt_local_other (P Q : HeightOneSpectrum (𝓞 K)) (hPQ : P ≠ Q)
    (g : SourceFiniteKP2Projective K hζ Q) :
    sourceKPAdelicProjectiveAt K hζ P (sourceKPAdelicLocalProjective K hζ Q g) = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (sourceFiniteKP2Scalar K hζ Q).range g
  change ProjGenLinGroup.mk (sourceKPAdeleMatrixAt K P (sourceKPAdeleSingleMatrix K Q x.base)) = 1
  rw [sourceKPAdeleSingleMatrix_other K Q P hPQ, ProjGenLinGroup.mk_one]

variable (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (SourceExteriorPrime K S₀))

theorem sourceKPAdelicFiniteProduct_at (P : T)
    (g : (Q : T) → SourceFiniteKP2Projective K hζ Q.val.val) :
    sourceKPAdelicProjectiveAt K hζ P.val.val (sourceKPAdelicFiniteProduct K hζ S₀ T g) =
      sourceFiniteKP2ProjectiveProjection K hζ P.val.val (g P) := by
  have he :
      (sourceKPAdelicProjectiveAt K hζ P.val.val).comp (sourceKPAdelicFiniteProduct K hζ S₀ T) =
        (sourceFiniteKP2ProjectiveProjection K hζ P.val.val).comp (Pi.evalMonoidHom _ P) := by
    apply MonoidHom.pi_ext
    intro Q x
    change sourceKPAdelicProjectiveAt K hζ P.val.val
      (sourceKPAdelicFiniteProduct K hζ S₀ T (Pi.mulSingle (M := fun R : T => SourceFiniteKP2Projective K hζ R.val.val) Q x)) =
        sourceFiniteKP2ProjectiveProjection K hζ P.val.val ((Pi.mulSingle (M := fun R : T => SourceFiniteKP2Projective K hζ R.val.val) Q x) P)
    rw [sourceKPAdelicFiniteProduct_single]
    by_cases hPQ : P = Q
    · subst Q
      rw [Pi.mulSingle_eq_same, sourceKPAdelicProjectiveAt_local_same]
    · rw [Pi.mulSingle_eq_of_ne hPQ, map_one]
      exact sourceKPAdelicProjectiveAt_local_other K hζ P.val.val Q.val.val
        (fun he => hPQ (Subtype.ext (Subtype.ext he))) x
  exact DFunLike.congr_fun he g

theorem sourceKPAdelicFiniteProduct_centers
    (z : (P : T) → rootsOfUnity 3 (P.val.val.adicCompletion K)) :
    sourceKPAdelicFiniteProduct K hζ S₀ T
      (fun P => sourceFiniteKP2ProjectiveCenter K hζ P.val.val (z P)) =
      sourceKPAdelicProjectiveCenter K hζ
        (∏ P : T, (sourceKPRootsTransport K hζ P.val.val).symm (z P)) := by
  let zs (P : T) := (sourceKPRootsTransport K hζ P.val.val).symm (z P)
  let f (P : T) := sourceKPAdelicLocalProjective K hζ P.val.val
    (sourceFiniteKP2ProjectiveCenter K hζ P.val.val (z P))
  have hcomm : Set.Pairwise (↑(Finset.univ : Finset T)) (fun i j => Commute (f i) (f j)) := by
    intro P _ Q _ hPQ
    exact sourceKPAdelicLocalProjective_commute K hζ P.val.val Q.val.val
      (fun h => hPQ (Subtype.ext (Subtype.ext h.symm))) _ _
  change Finset.univ.noncommProd f hcomm = _
  calc
    _ = Finset.univ.noncommProd (fun P : T => sourceKPAdelicProjectiveCenter K hζ (zs P))
          (by intro i _ j _ _; exact (Commute.all (zs i) (zs j)).map _) := by
      apply Finset.noncommProd_congr
      · rfl
      · intro P _
        exact sourceKPAdelicLocalProjective_center K hζ P.val.val (z P)
    _ = sourceKPAdelicProjectiveCenter K hζ
          (Finset.univ.noncommProd zs (by intro i _ j _ _; exact Commute.all _ _)) :=
      (Finset.map_noncommProd _ zs _ (sourceKPAdelicProjectiveCenter K hζ)).symm
    _ = _ := by rw [Finset.noncommProd_eq_prod]

theorem sourceKPAdelicFiniteProduct_kernel
    (g : (P : T) → SourceFiniteKP2Projective K hζ P.val.val)
    (hg : sourceKPAdelicFiniteProduct K hζ S₀ T g = 1) :
    ∃ z : (P : T) → rootsOfUnity 3 (P.val.val.adicCompletion K),
      (∀ P, g P = sourceFiniteKP2ProjectiveCenter K hζ P.val.val (z P)) ∧
        (∏ P : T, (sourceKPRootsTransport K hζ P.val.val).symm (z P)) = 1 := by
  have hloc (P : T) : ∃ z, g P = sourceFiniteKP2ProjectiveCenter K hζ P.val.val z := by
    have he := sourceKPAdelicFiniteProduct_at K hζ S₀ T P g
    rw [hg, map_one] at he
    have hm : g P ∈ (sourceFiniteKP2ProjectiveProjection K hζ P.val.val).ker := he.symm
    rw [← sourceFiniteKP2Projective_exact] at hm
    obtain ⟨z, hz⟩ := hm
    exact ⟨z, hz.symm⟩
  choose z hz using hloc
  refine ⟨z, hz, ?_⟩
  have he : g = fun P => sourceFiniteKP2ProjectiveCenter K hζ P.val.val (z P) := funext hz
  rw [he, sourceKPAdelicFiniteProduct_centers] at hg
  exact (sourceKPAdelicProjectiveCenter_injective K hζ) (hg.trans (map_one _).symm)

end
end ArtinMatthews
