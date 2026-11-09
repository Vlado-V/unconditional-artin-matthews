module

public import ArtinMatthews.SourceKPCompactLevelContainer
public import ArtinMatthews.SourceKPAdelicBorelBand


set_option backward.privateInPublic true
@[expose] public section

/-! Every representative in an actual height band has an equivalent
representative whose matrix lies in the fixed Borel band times base compact. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing Pointwise
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAutomorphicLevelMk_rational
    (γ : PGL(2, K)) (q : SourceKPAdelicProjective K hζ) :
    sourceKPAutomorphicLevelMk K hζ (sourceKPAdelicProjectiveRationalLift K hζ γ * q) =
      sourceKPAutomorphicLevelMk K hζ q := by
  apply Quotient.sound
  apply MulAction.mem_orbit_iff.mpr
  exact ⟨γ,rfl⟩

def sourceKPHeightBandMatrices (v₀ : InfinitePlace K) (a b : ℝ) :
    Set (GL (Fin 2) 𝔸[K]) :=
  sourceKPAdelicBorelBand K hζ v₀ a b * (SourceKPAdelicBaseCompactMatrix K hζ : Set _)

theorem sourceKPHeightBand_matrix_reduction
    (v₀ : InfinitePlace K) (a b : ℝ) (g : GL (Fin 2) 𝔸[K])
    (hg : Real.log (sourceKPAdelicHeight K hζ g) ∈ Set.Icc a b) :
    ∃ (γ : PGL(2,K)) (g' : GL (Fin 2) 𝔸[K]),
      g' ∈ sourceKPHeightBandMatrices K hζ v₀ a b ∧
      ProjGenLinGroup.map (algebraMap K 𝔸[K]) γ * ProjGenLinGroup.mk g =
        ProjGenLinGroup.mk g' := by
  let B := sourceKPAdelicIwasawaBorel K hζ g
  let C := sourceKPAdelicIwasawaCompact K hζ g
  have hB : B ∈ sourceKPRingNormalizedBorel 𝔸[K] := sourceKPAdelicIwasawaBorel_mem K hζ g
  have hC : C ∈ SourceKPAdelicBaseCompactMatrix K hζ := sourceKPAdelicIwasawaCompact_mem K hζ g
  have hheight : sourceKPAdelicHeight K hζ g = sourceKPIdeleAbsoluteNorm K (GeneralLinearGroup.det B) :=
    sourceKPAdelicHeight_factor K hζ g B C (sourceKPAdelicIwasawaScalar K hζ g)
      hB hC (sourceKPAdelicIwasawa_factor K hζ g)
  have hb : B = sourceKPUpperMatrix 𝔸[K] (B 0 1) *
      sourceKPDiagonalHom 𝔸[K] (GeneralLinearGroup.det B) := sourceKPRingNormalizedBorel_factor 𝔸[K] B hB
  obtain ⟨u,r,hr⟩ := sourceKPAdelicBorelBand_reduce K hζ v₀ a b (B 0 1)
    (GeneralLinearGroup.det B) (by simpa only [hheight] using hg)
  rw [← hb] at hr
  let γ₀ := sourceKPUpperMatrix K r * sourceKPDiagonalHom K u
  let γa := GeneralLinearGroup.map (algebraMap K 𝔸[K]) γ₀
  refine ⟨ProjGenLinGroup.mk γ₀,γa * B * C,Set.mul_mem_mul hr hC,?_⟩
  have hp : ProjGenLinGroup.mk g = ProjGenLinGroup.mk (B*C) := by
    conv_lhs => rw [sourceKPAdelicIwasawa_factor K hζ g]
    simp only [map_mul, ProjGenLinGroup.mk_scalar, mul_one, B, C]
  rw [ProjGenLinGroup.map_mk, hp, ← map_mul]
  exact congrArg ProjGenLinGroup.mk (mul_assoc γa B C).symm

theorem sourceKPHeightBand_cover_reduction
    (v₀ : InfinitePlace K) (a b : ℝ) (q : SourceKPAdelicProjective K hζ)
    (g : GL (Fin 2) 𝔸[K])
    (hq : sourceKPAdelicProjectiveProjection K hζ q = ProjGenLinGroup.mk g)
    (hg : Real.log (sourceKPAdelicHeight K hζ g) ∈ Set.Icc a b) :
    sourceKPAutomorphicLevelMk K hζ q ∈
      sourceKPCompactAutomorphicContainer K hζ (sourceKPHeightBandMatrices K hζ v₀ a b) := by
  obtain ⟨γ,g',hg',he⟩ := sourceKPHeightBand_matrix_reduction K hζ v₀ a b g hg
  have hq' : sourceKPAdelicProjectiveProjection K hζ
      (sourceKPAdelicProjectiveRationalLift K hζ γ * q) = ProjGenLinGroup.mk g' := by
    rw [map_mul,sourceKPAdelicProjectiveRationalLift_projection,hq]
    exact he
  have hm := sourceKPCompactAutomorphicContainer_mem K hζ
    (sourceKPHeightBandMatrices K hζ v₀ a b)
      (sourceKPAdelicProjectiveRationalLift K hζ γ * q) g' hg' hq'
  simpa only [sourceKPAutomorphicLevelMk_rational] using hm

end
end ArtinMatthews
