module

public import ArtinMatthews.SourceArchNormalizedProductC2
public import ArtinMatthews.SourceKPAdelicEisensteinProductC1
public import Mathlib.Algebra.Lie.OfAssociative


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform second-derivative bounds for actual adelic rational summands. -/

namespace ArtinMatthews
open NumberField Matrix OAI.CubicEisenstein SourceArchJacquet Filter
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicProductSection_second_bound (s : ℂ)
    (S : Set (InfinitePlace K → EuclideanSpatial)) (hS : IsCompact S)
    (hpos : ∀ p ∈ S, ∀ v, 0 < p v 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : SourceKPAdelicProjective K hζ), ∀ p ∈ S,
      ‖fderiv ℝ (fderiv ℝ (sourceKPAdelicProductSection K hζ s q)) p‖ ≤
        C*‖sourceKPAdelicProductSection K hζ s q p‖ := by
  obtain ⟨C,hC,hbound⟩ :=
    sourceArchTranslatedCoordinateProduct_iteratedFDeriv_two_le_of_isCompact s S hS hpos
  refine ⟨C,hC,?_⟩
  rintro ⟨a,qf⟩ p hp
  obtain ⟨g,rfl⟩ := ProjGenLinGroup.mk_surjective a
  let A := fun v => sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)
  let F := sourceArchTranslatedCoordinateProduct s A
  let c := sourceKPAdelicCompactScalar K hζ s (1,qf)
  have he : sourceKPAdelicProductSection K hζ s (ProjGenLinGroup.mk g,qf) =ᶠ[𝓝 p]
      fun x => c • F x := by
    filter_upwards [sourceKPAdelicProductSection_eventually_factor K hζ s g qf p (hpos p hp)] with x hx
    exact hx.trans (mul_comm _ _)
  have hF : ContDiffAt ℝ 2 F p :=
    (sourceArchTranslatedCoordinateProduct_contDiffAt s A p (hpos p hp)).of_le (by simp)
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv,
    (he.iteratedFDeriv ℝ 2).eq_of_nhds,iteratedFDeriv_const_smul_apply' hF,norm_smul,
    he.eq_of_nhds,norm_smul]
  exact (mul_le_mul_of_nonneg_left (hbound A p hp) (norm_nonneg c)).trans_eq (by ring)

theorem sourceKPAdelicRationalProductChart_compact_second_bound {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (q : SourceKPAdelicProjective K hζ) (S : Set (InfinitePlace K → EuclideanSpatial))
    (hS : IsCompact S) (hpos : ∀ p ∈ S, ∀ v, 0 < p v 2) :
    ∃ M : SourceKPRationalBorelCoset K → ℝ, Summable M ∧
      ∀ c p, p ∈ S → ‖fderiv ℝ (fderiv ℝ
        (sourceKPAdelicRationalProductChart K hζ s q c)) p‖ ≤ M c := by
  obtain ⟨M,hM,hbound⟩ := sourceKPAdelicRationalProductChart_compact_bound K hζ hs q S hS hpos
  obtain ⟨C,hC,hsecond⟩ := sourceKPAdelicProductSection_second_bound K hζ s S hS hpos
  refine ⟨fun c => C*M c,hM.mul_left C,?_⟩
  intro c p hp
  have h := hbound c p hp
  have hd : ‖fderiv ℝ (fderiv ℝ (sourceKPAdelicRationalProductChart K hζ s q c)) p‖ ≤
      C*‖sourceKPAdelicRationalProductChart K hζ s q c p‖ := by
    induction c using Quotient.inductionOn with
    | _ γ =>
      have hγ := hsecond (sourceKPAdelicProjectiveRationalLift K hζ γ*q) p hp
      rw [← sourceKPAdelicRationalProductChart_mk] at hγ
      exact hγ
  exact hd.trans (mul_le_mul_of_nonneg_left h hC)

end
end ArtinMatthews
