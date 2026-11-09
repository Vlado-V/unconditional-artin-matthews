module

public import ArtinMatthews.SourceKPArithmeticUpperQuotient
public import ArtinMatthews.SourceKPAutomorphicHeightCompact
public import ArtinMatthews.SourceArchOnlyCompact


set_option backward.privateInPublic true
@[expose] public section

/-! The actual rational-orbit height descends to the compact archimedean
quotient and has compact sublevels there. -/
namespace ArtinMatthews
open NumberField Matrix Topology MulOpposite SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPArchCompactRight_deep (k : SourceKPArchCompactRightGroup K hζ) :
    (unop k.val,1) ∈ sourceKPAdelicDeepCompact K hζ := by
  have hk : unop k.val ∈ sourceKPArchBaseCompactSubgroup K hζ := k.property
  obtain ⟨u,hu⟩ := (sourceKPArchBaseCompactSubgroup_mem_iff K hζ _).mp hk
  have hg (v : InfinitePlace K) :
      sourceKPArchMatrixComplexEquiv K hζ v
        (sourceArchGLPiEquiv K (sourceKPArchUnitaryMatrix K hζ u) v) ∈
          SourceArchJacquet.sourceArchUnitaryGL.range := by
    rw [sourceKPArchUnitaryMatrix_at]
    exact ⟨u v,rfl⟩
  have hd := (sourceArchOnlyCompact K hζ (sourceKPArchUnitaryMatrix K hζ u) hg).property
  change (ProjGenLinGroup.mk (sourceKPArchUnitaryMatrix K hζ u),1) ∈
    sourceKPAdelicDeepCompact K hζ at hd
  rw [← hu] at hd
  exact hd

theorem sourceKPAdelicOrbitHeight_archPair
    (k : SourceKPArchCompactRightGroup K hζ) (q : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicOrbitHeight K hζ (q.1 * unop k.val,q.2) = sourceKPAdelicOrbitHeight K hζ q := by
  have h := sourceKPAdelicOrbitHeight_right_deep K hζ q
    ⟨(unop k.val,1),sourceKPArchCompactRight_deep K hζ k⟩
  have hp : q * ((unop k.val,1) : SourceKPAdelicProjective K hζ) =
      (q.1 * unop k.val,q.2) := Prod.ext rfl (mul_one q.2)
  exact (congrArg (sourceKPAdelicOrbitHeight K hζ) hp).symm.trans h

theorem sourceKPAutomorphicOrbitHeight_rightCompact
    (k : SourceKPArchCompactRightGroup K hζ) (x : SourceKPAutomorphicLevel K hζ) :
    sourceKPAutomorphicOrbitHeight K hζ (k • x) = sourceKPAutomorphicOrbitHeight K hζ x := by
  obtain ⟨q,rfl⟩ := sourceKPAutomorphicLevelMk_surjective K hζ x
  calc
    sourceKPAutomorphicOrbitHeight K hζ (k • sourceKPAutomorphicLevelMk K hζ q) =
        sourceKPAutomorphicOrbitHeight K hζ
          (sourceKPAutomorphicLevelMk K hζ (q.1 * unop k.val,q.2)) :=
      congrArg (sourceKPAutomorphicOrbitHeight K hζ)
        (sourceKPAutomorphicLevelMk_archRight K hζ k.val q)
    _ = sourceKPAutomorphicOrbitHeight K hζ (sourceKPAutomorphicLevelMk K hζ q) := by
      rw [sourceKPAutomorphicOrbitHeight_mk, sourceKPAutomorphicOrbitHeight_mk]
      exact sourceKPAdelicOrbitHeight_archPair K hζ k q

def sourceKPAutomorphicCompactOrbitHeight : SourceKPAutomorphicCompactLevel K hζ → ℝ :=
  Quotient.lift (sourceKPAutomorphicOrbitHeight K hζ) (by
    intro x y hxy
    obtain ⟨k,hk⟩ := MulAction.mem_orbit_iff.mp hxy
    rw [← hk]
    exact sourceKPAutomorphicOrbitHeight_rightCompact K hζ k y)

@[simp] theorem sourceKPAutomorphicCompactOrbitHeight_mk (x : SourceKPAutomorphicLevel K hζ) :
    sourceKPAutomorphicCompactOrbitHeight K hζ (sourceKPAutomorphicCompactMk K hζ x) =
      sourceKPAutomorphicOrbitHeight K hζ x := rfl

theorem sourceKPAutomorphicCompactOrbitHeight_sublevel_eq_image (T : ℝ) :
    {x : SourceKPAutomorphicCompactLevel K hζ | sourceKPAutomorphicCompactOrbitHeight K hζ x ≤ T} =
      sourceKPAutomorphicCompactMk K hζ ''
        {x : SourceKPAutomorphicLevel K hζ | sourceKPAutomorphicOrbitHeight K hζ x ≤ T} := by
  ext x
  constructor
  · intro hx
    induction x using Quotient.inductionOn with
    | _ x => exact ⟨x,hx,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    exact hx

theorem sourceKPAutomorphicCompactOrbitHeight_sublevel_isCompact (T : ℝ) :
    IsCompact {x : SourceKPAutomorphicCompactLevel K hζ |
      sourceKPAutomorphicCompactOrbitHeight K hζ x ≤ T} := by
  rw [sourceKPAutomorphicCompactOrbitHeight_sublevel_eq_image]
  exact (sourceKPAutomorphicOrbitHeight_sublevel_isCompact K hζ T).image
    (sourceKPAutomorphicCompactMk_isOpenQuotientMap K hζ).continuous

theorem sourceKPAutomorphicCompactOrbitHeight_lowerSemicontinuous :
    LowerSemicontinuous (sourceKPAutomorphicCompactOrbitHeight K hζ) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro T
  apply (sourceKPAutomorphicCompactMk_isOpenQuotientMap K hζ).isQuotientMap.isClosed_preimage.mp
  change IsClosed {x : SourceKPAutomorphicLevel K hζ |
    sourceKPAutomorphicCompactOrbitHeight K hζ (sourceKPAutomorphicCompactMk K hζ x) ≤ T}
  simpa only [sourceKPAutomorphicCompactOrbitHeight_mk] using
    sourceKPAutomorphicOrbitHeight_sublevel_closed K hζ T

theorem sourceKPAutomorphicCompactOrbitHeight_uniform_pos :
    ∃ c : ℝ, 0 < c ∧ ∀ x : SourceKPAutomorphicCompactLevel K hζ,
      c ≤ sourceKPAutomorphicCompactOrbitHeight K hζ x := by
  obtain ⟨c,hc,h⟩ := sourceKPAutomorphicOrbitHeight_uniform_pos K hζ
  refine ⟨c,hc,fun x => ?_⟩
  induction x using Quotient.inductionOn with
  | _ x => exact h x

theorem sourceKPAutomorphicCompactOrbitHeight_exhaustion_covers :
    (⋃ n : ℕ, {x : SourceKPAutomorphicCompactLevel K hζ |
      sourceKPAutomorphicCompactOrbitHeight K hζ x ≤ (n : ℝ)}) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨n,hn⟩ := exists_nat_gt (sourceKPAutomorphicCompactOrbitHeight K hζ x)
  exact Set.mem_iUnion.mpr ⟨n,hn.le⟩

end
end ArtinMatthews
