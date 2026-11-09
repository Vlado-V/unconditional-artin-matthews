module

public import ArtinMatthews.SourceKPAdelicRadialCasimir


set_option backward.privateInPublic true
@[expose] public section

/-! Actual radial sections have two derivatives along the right paths
used by the adelic Casimir. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open SourceArchJacquet
open scoped NumberField AdeleRing MatrixGroups ContDiff
noncomputable section

private theorem radialPath_twice (φ H L M : ℝ → ℝ) (β : ℂ) (F : ℝ → ℂ)
    (hφ : ContDiff (ℝ) (2 : ℕ∞ω) φ)
    (hH : ∀ t, HasDerivAt H (2*H t*L t) t)
    (hL : ∀ t, HasDerivAt L (M t) t)
    (hF : ∀ t, HasDerivAt F (β*(L t : ℂ)*F t) t) :
    Differentiable ℝ (sourceKPRadialPath φ H F) ∧
      Differentiable ℝ (deriv (sourceKPRadialPath φ H F)) := by
  have hfirst (t : ℝ) := sourceKPRadialPath_hasDerivAt φ H L β F t
    ((hφ.differentiable (by norm_num)).differentiableAt) (hH t) (hF t)
  refine ⟨fun t => (hfirst t).differentiableAt,?_⟩
  have he : deriv (sourceKPRadialPath φ H F) = sourceKPRadialPathOne φ H L β F :=
    funext (fun t => (hfirst t).deriv)
  rw [he]
  exact fun t => (sourceKPRadialPathOne_hasDerivAt φ H L M β F t hφ (hH t) (hL t) (hF t)).differentiableAt

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicRadialSection_upper_twice (φ : ℝ → ℝ) (s : ℂ)
    (hφ : ContDiff (ℝ) (2 : ℕ∞ω) φ) (q : SourceKPAdelicProjective K hζ)
    (v : InfinitePlace K) (z : ℂ) :
    Differentiable ℝ (sourceArchGlobalUpperTranslate K hζ (sourceKPAdelicRadialSection K hζ φ s) q v z) ∧
      Differentiable ℝ (deriv (sourceArchGlobalUpperTranslate K hζ
        (sourceKPAdelicRadialSection K hζ φ s) q v z)) := by
  have := source_isTotallyComplex K hζ
  rcases q with ⟨qI,qf⟩
  obtain ⟨g,rfl⟩ := ProjGenLinGroup.mk_surjective qI
  obtain ⟨u,hu⟩ := ProjGenLinGroup.mk_surjective (sourceKPFiniteAdeleProjectiveProjection K hζ qf)
  let a := sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)
  let A := sourceKPAdelicOtherArchHeight K hζ g u v
  let c := sourceArchOtherScalar K hζ s g qf v
  have he : sourceArchGlobalUpperTranslate K hζ (sourceKPAdelicRadialSection K hζ φ s)
      (ProjGenLinGroup.mk g,qf) v z = fun t => sourceKPRadialUpperSection φ A s a z t*c := by
    funext t
    unfold sourceArchGlobalUpperTranslate sourceKPAdelicRadialSection
    rw [sourceKPAdelicCoverHeight_single_factor K hζ g qf u hu.symm,
      NumberField.IsTotallyComplex.mult_eq,sourceArchCompactScalar_single_right]
    unfold sourceKPRadialUpperSection sourceKPRadialPath sourceKPRadialUpperHeight sourceArchUpperSection
    change (φ (sourceArchHeight (a*sourceKPUpperMatrix ℂ ((t : ℂ)*z))^2*A) : ℂ)*
      (sourceArchSphericalGL s (a*sourceKPUpperMatrix ℂ ((t : ℂ)*z))*c) = _
    rw [mul_comm (sourceArchHeight (a*sourceKPUpperMatrix ℂ ((t : ℂ)*z))^2) A]
    ring
  have hd := radialPath_twice φ (sourceKPRadialUpperHeight A a z)
    (sourceArchUpperLogOne a z) (sourceArchUpperLogTwo a z) (2*s+1)
    (sourceArchUpperSection s a z) hφ (sourceKPRadialUpperHeight_hasDerivAt A a z)
    (sourceArchUpperLogOne_hasDerivAt a z) (sourceArchUpperSection_hasDerivAt s a z)
  rw [he]
  refine ⟨hd.1.mul_const c,?_⟩
  rw [deriv_mul_const_field']
  exact hd.2.mul_const c

theorem sourceKPAdelicRadialSection_diagonal_twice (φ : ℝ → ℝ) (s : ℂ)
    (hφ : ContDiff (ℝ) (2 : ℕ∞ω) φ) (q : SourceKPAdelicProjective K hζ)
    (v : InfinitePlace K) :
    Differentiable ℝ (sourceArchGlobalDiagonalTranslate K hζ (sourceKPAdelicRadialSection K hζ φ s) q v) ∧
      Differentiable ℝ (deriv (sourceArchGlobalDiagonalTranslate K hζ
        (sourceKPAdelicRadialSection K hζ φ s) q v)) := by
  have := source_isTotallyComplex K hζ
  rcases q with ⟨qI,qf⟩
  obtain ⟨g,rfl⟩ := ProjGenLinGroup.mk_surjective qI
  obtain ⟨u,hu⟩ := ProjGenLinGroup.mk_surjective (sourceKPFiniteAdeleProjectiveProjection K hζ qf)
  let a := sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)
  let A := sourceKPAdelicOtherArchHeight K hζ g u v
  let c := sourceArchOtherScalar K hζ s g qf v
  have he : sourceArchGlobalDiagonalTranslate K hζ (sourceKPAdelicRadialSection K hζ φ s)
      (ProjGenLinGroup.mk g,qf) v = fun t => sourceKPRadialDiagonalSection φ A s a t*c := by
    funext t
    unfold sourceArchGlobalDiagonalTranslate sourceKPAdelicRadialSection
    rw [sourceKPAdelicCoverHeight_single_factor K hζ g qf u hu.symm,
      NumberField.IsTotallyComplex.mult_eq,sourceArchCompactScalar_single_right]
    unfold sourceKPRadialDiagonalSection sourceKPRadialPath sourceKPRadialDiagonalHeight sourceArchDiagonalSection
    change (φ (sourceArchHeight (a*sourceArchPositiveDiagonal t)^2*A) : ℂ)*
      (sourceArchSphericalGL s (a*sourceArchPositiveDiagonal t)*c) = _
    rw [mul_comm (sourceArchHeight (a*sourceArchPositiveDiagonal t)^2) A]
    ring
  have hd := radialPath_twice φ (sourceKPRadialDiagonalHeight A a)
    (sourceArchDiagonalLogOne a) (sourceArchDiagonalLogTwo a) (2*s+1)
    (sourceArchDiagonalSection s a) hφ (sourceKPRadialDiagonalHeight_hasDerivAt A a)
    (sourceArchDiagonalLogOne_hasDerivAt a) (sourceArchDiagonalSection_hasDerivAt s a)
  rw [he]
  refine ⟨hd.1.mul_const c,?_⟩
  rw [deriv_mul_const_field']
  exact hd.2.mul_const c

end
end ArtinMatthews
