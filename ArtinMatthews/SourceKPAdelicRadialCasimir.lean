module

public import ArtinMatthews.SourceKPArchRadialCasimir
public import ArtinMatthews.SourceKPAdelicHeightUpperChart
public import ArtinMatthews.SourceArchRightCasimir


set_option backward.privateInPublic true
@[expose] public section

/-! The radial Casimir formula on the actual adelic cubic cover. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open SourceArchJacquet
open scoped NumberField AdeleRing MatrixGroups ContDiff
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicRadialSection (φ : ℝ → ℝ) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) : ℂ :=
  (φ (sourceKPAdelicCoverHeight K hζ q) : ℂ)*sourceKPAdelicCompactScalar K hζ s q

theorem sourceKPAdelicRadialSection_casimir (φ : ℝ → ℝ) (s : ℂ)
    (hφ : ContDiff (ℝ) (2 : ℕ∞ω) φ) (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K) :
    sourceArchGlobalCasimir K hζ (sourceKPAdelicRadialSection K hζ φ s) q v =
      (1-4*s^2)*sourceKPAdelicRadialSection K hζ φ s q +
        (-(4*(sourceKPAdelicCoverHeight K hζ q)^2*
              deriv (deriv φ) (sourceKPAdelicCoverHeight K hζ q) : ℝ) -
          (8*s+4)*(sourceKPAdelicCoverHeight K hζ q : ℂ)*
            ((deriv φ (sourceKPAdelicCoverHeight K hζ q) : ℝ) : ℂ)) *
              sourceKPAdelicCompactScalar K hζ s q := by
  have := source_isTotallyComplex K hζ
  rcases q with ⟨qI,qf⟩
  obtain ⟨g,rfl⟩ := ProjGenLinGroup.mk_surjective qI
  obtain ⟨u,hu⟩ := ProjGenLinGroup.mk_surjective (sourceKPFiniteAdeleProjectiveProjection K hζ qf)
  let a := sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)
  let A := sourceKPAdelicOtherArchHeight K hζ g u v
  let c := sourceArchOtherScalar K hζ s g qf v
  have hheight (b : GL (Fin 2) ℂ) :
      sourceKPAdelicCoverHeight K hζ ((ProjGenLinGroup.mk g,qf)*sourceArchGroupSingle K hζ v b) =
        A*(sourceArchHeight (a*b))^2 := by
    rw [sourceKPAdelicCoverHeight_single_factor K hζ g qf u hu.symm,
      NumberField.IsTotallyComplex.mult_eq]
    exact mul_comm _ _
  have hscalar (b : GL (Fin 2) ℂ) :
      sourceKPAdelicCompactScalar K hζ s ((ProjGenLinGroup.mk g,qf)*sourceArchGroupSingle K hζ v b) =
        sourceArchSphericalGL s (a*b)*c :=
    sourceArchCompactScalar_single_right K hζ s g qf v b
  have hU (z : ℂ) : sourceArchGlobalUpperTranslate K hζ
      (sourceKPAdelicRadialSection K hζ φ s) (ProjGenLinGroup.mk g,qf) v z =
        fun t => sourceKPRadialUpperSection φ A s a z t*c := by
    funext t
    unfold sourceArchGlobalUpperTranslate sourceKPAdelicRadialSection
    rw [hheight,hscalar]
    unfold sourceKPRadialUpperSection sourceKPRadialPath sourceKPRadialUpperHeight sourceArchUpperSection
    ring
  have hA : sourceArchGlobalDiagonalTranslate K hζ
      (sourceKPAdelicRadialSection K hζ φ s) (ProjGenLinGroup.mk g,qf) v =
        fun t => sourceKPRadialDiagonalSection φ A s a t*c := by
    funext t
    unfold sourceArchGlobalDiagonalTranslate sourceKPAdelicRadialSection
    rw [hheight,hscalar]
    unfold sourceKPRadialDiagonalSection sourceKPRadialPath sourceKPRadialDiagonalHeight sourceArchDiagonalSection
    ring
  have hbase : sourceKPAdelicCoverHeight K hζ (ProjGenLinGroup.mk g,qf) =
      A*(sourceArchHeight a)^2 := by
    simpa only [sourceArchGroupSingle_one,mul_one] using hheight 1
  rw [sourceArchGlobalCasimir,hU 1,hU Complex.I,hA]
  simp only [deriv_mul_const_field',deriv_mul_const_field]
  calc
    _ = sourceKPRadialSphericalCasimir φ A s a*c := by
      unfold sourceKPRadialSphericalCasimir
      ring
    _ = _ := by
      rw [sourceKPRadialSphericalCasimir_eq φ A s a hφ,sourceKPAdelicRadialSection,
        hbase,sourceArchCompactScalar_single_base K hζ s g qf v]
      unfold sourceKPRadialSphericalSection
      ring

end
end ArtinMatthews
