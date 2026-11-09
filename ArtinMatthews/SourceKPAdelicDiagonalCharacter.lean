module

public import ArtinMatthews.SourceKPAdelicParametricRational


set_option backward.privateInPublic true
@[expose] public section

/-! The parameter character on ordinary diagonal sections inside the
rational-cube torus. Norm-one diagonal sections have trivial character,
which supplies the intersection condition for compact torus vectors. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicCubeRational_join_factor (z : rootsOfUnity 3 K)
    (c : SourceKPIdeleCubes K) (a : Kˣ) :
    sourceKPAdelicRationalCubeJoin K hζ (sourceKPAdelicCubeTorusEquiv K hζ (z,c),a) =
      sourceKPAdelicProjectiveCenter K hζ z * sourceKPAdelicProjectiveDiagonalLift K hζ
        (c.val * IdeleGroup.unitEmbedding (𝓞 K) K a) := by
  change (sourceKPAdelicCubeTorusEquiv K hζ (z,c)).val *
      sourceKPAdelicProjectiveRationalLift K hζ (sourceKPProjectiveDiagonalHom K a) = _
  rw [sourceKPAdelicCubeTorusEquiv_val, sourceKPAdelicProjectiveRationalLift_diagonal]
  change (sourceKPAdelicProjectiveCenter K hζ z * sourceKPAdelicProjectiveDiagonalLift K hζ c.val) *
    sourceKPAdelicProjectiveDiagonalLift K hζ (IdeleGroup.unitEmbedding (𝓞 K) K a) = _
  obtain ⟨b,hb⟩ := c.property
  change b^3 = c.val at hb
  rw [← hb, mul_assoc, sourceKPAdelicProjectiveDiagonalLift_cube_mul_left]

theorem sourceKPAdelicParametricRationalCharacter_diagonal (s : ℂ)
    (t : sourceKPAdelicRationalCubeTorus K hζ) (u : IdeleGroup (𝓞 K) K)
    (htu : t.val = sourceKPAdelicProjectiveDiagonalLift K hζ u) :
    sourceKPAdelicParametricRationalCharacter K hζ s t = sourceKPIdeleComplexNorm K s u := by
  obtain ⟨p,hp⟩ := t.property
  obtain ⟨q,hq⟩ := (sourceKPAdelicCubeTorusEquiv K hζ).surjective p.1
  rcases q with ⟨z,c⟩
  have hfactor : sourceKPAdelicProjectiveCenter K hζ z *
      sourceKPAdelicProjectiveDiagonalLift K hζ
        (c.val * IdeleGroup.unitEmbedding (𝓞 K) K p.2) =
      sourceKPAdelicProjectiveDiagonalLift K hζ u := by
    rw [← sourceKPAdelicCubeRational_join_factor K hζ z c p.2, hq]
    exact hp.trans htu
  have hcoord : c.val * IdeleGroup.unitEmbedding (𝓞 K) K p.2 = u := by
    apply sourceKPProjectiveDiagonalHom_injective 𝔸[K]
    have h := congrArg (sourceKPAdelicProjectiveProjection K hζ) hfactor
    rw [map_mul, sourceKPAdelicProjectiveCenter_projection_one, one_mul,
      sourceKPAdelicProjectiveDiagonalLift_projection,
      sourceKPAdelicProjectiveDiagonalLift_projection] at h
    exact h
  have hz : z = 1 := by
    apply sourceKPAdelicProjectiveCenter_injective K hζ
    rw [hcoord] at hfactor
    have hzero : sourceKPAdelicProjectiveCenter K hζ z = 1 :=
      mul_right_cancel (show sourceKPAdelicProjectiveCenter K hζ z *
          sourceKPAdelicProjectiveDiagonalLift K hζ u =
        1 * sourceKPAdelicProjectiveDiagonalLift K hζ u by simpa only [one_mul] using hfactor)
    simpa only [map_one] using hzero
  have ht : (⟨sourceKPAdelicRationalCubeJoin K hζ p, ⟨p,rfl⟩⟩ :
      sourceKPAdelicRationalCubeTorus K hζ) = t := Subtype.ext hp
  rw [← ht, sourceKPAdelicParametricRationalCharacter_join, ← hq,
    sourceKPAdelicParametricCharacter_equiv, hz, map_one, one_mul]
  have hn : sourceKPIdeleComplexNorm K s (c.val * IdeleGroup.unitEmbedding (𝓞 K) K p.2) =
      sourceKPIdeleComplexNorm K s c.val := by
    rw [map_mul, sourceKPIdeleComplexNorm_principal, mul_one]
  rw [← hn, hcoord]

theorem sourceKPAdelicParametricRationalCharacter_diagonal_norm_one (s : ℂ)
    (t : sourceKPAdelicRationalCubeTorus K hζ) (u : IdeleGroup (𝓞 K) K)
    (htu : t.val = sourceKPAdelicProjectiveDiagonalLift K hζ u)
    (hu : sourceKPIdeleAbsoluteNorm K u = 1) :
    sourceKPAdelicParametricRationalCharacter K hζ s t = 1 := by
  rw [sourceKPAdelicParametricRationalCharacter_diagonal K hζ s t u htu]
  apply Units.ext
  rw [sourceKPIdeleComplexNorm_coe, hu, Real.log_one, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, Units.val_one]

end
end ArtinMatthews
