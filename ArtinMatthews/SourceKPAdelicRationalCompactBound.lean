module

public import ArtinMatthews.SourceKPAdelicOrbitHeightCompact
public import ArtinMatthews.SourceKPAdelicEisensteinConvergence


set_option backward.privateInPublic true
@[expose] public section

/-! A single summable bound for the actual rational Eisenstein terms
over all cover lifts of a compact set of adelic matrices. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicRationalSummand_compact_bound {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (S : Set (GL (Fin 2) 𝔸[K])) (hS : IsCompact S) :
    ∃ M : SourceKPRationalBorelCoset K → ℝ, Summable M ∧
      ∀ g ∈ S, ∀ q : SourceKPAdelicProjective K hζ,
        sourceKPAdelicProjectiveProjection K hζ q = ProjGenLinGroup.mk g →
        ∀ c, ‖sourceKPAdelicRationalSummand K hζ
          (sourceKPAdelicPrincipalSeriesScalar K hζ s (sourceKPAdelicCompactSection K hζ s)) q c‖ ≤ M c := by
  have hr : 0 ≤ s.re+1/2 := by
    have hn : 0 ≤ ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨B₁,_hB₁,hC⟩ := sourceKPAdelicHeightConstant_bounded K hζ S hS
  obtain ⟨B₂,_hB₂,hH⟩ := sourceKPAdelicOrbitHeight_bounded_on_matrices K hζ S hS
  let B : ℝ := max B₁ B₂
  let u : Option K → ℝ := fun t => match t with
    | none => B^(s.re+1/2)
    | some x => B^(s.re+1/2)*Height.mulHeight₁ x^(-(2*s.re+1))
  let e := sourceKPRationalBorelCosetEquiv K
  let M : SourceKPRationalBorelCoset K → ℝ := fun c => u (e.symm c)
  have hsome : Summable (fun x : K => u (some x)) :=
    (sourceKPRationalHeight_rpow_summable K hs).mul_left _
  let e₀ : Option K ≃ K ⊕ PUnit.{1} := Equiv.optionEquivSumPUnit K
  have hu₀ : Summable (fun t : K ⊕ PUnit.{1} => u (e₀.symm t)) := by
    apply Summable.sum
    · simpa only [e₀, Equiv.optionEquivSumPUnit_symm_inl, Function.comp_def] using hsome
    · exact (hasSum_fintype _).summable
  have hu : Summable u := e₀.symm.summable_iff.mp hu₀
  refine ⟨M,e.symm.summable_iff.mpr hu,?_⟩
  intro g hg q hq c
  obtain ⟨i,rfl⟩ := e.surjective c
  change ‖sourceKPAdelicRationalSummand K hζ
      (sourceKPAdelicPrincipalSeriesScalar K hζ s (sourceKPAdelicCompactSection K hζ s))
      q (sourceKPRationalBorelCosetEquiv K i)‖ ≤ u (e.symm (e i))
  rw [e.symm_apply_apply]
  cases i with
  | none =>
    have he : sourceKPAdelicRationalSummand K hζ
        (sourceKPAdelicPrincipalSeriesScalar K hζ s (sourceKPAdelicCompactSection K hζ s))
        q (sourceKPRationalBorelCosetEquiv K none) = sourceKPAdelicCompactScalar K hζ s q := by
      change sourceKPAdelicCompactScalar K hζ s
        (sourceKPAdelicProjectiveRationalLift K hζ (ProjGenLinGroup.mk (1 : GL (Fin 2) K))*q) = _
      rw [map_one,map_one,one_mul]
    rw [he]
    have hp : sourceKPAdelicCoverHeight K hζ q = sourceKPAdelicHeight K hζ g := by
      unfold sourceKPAdelicCoverHeight
      rw [hq,sourceKPAdelicHeightOnProjective_mk]
    have hb : sourceKPAdelicHeight K hζ g ≤ B := by
      rw [← hp]
      exact (sourceKPAdelicCoverHeight_le_orbit K hζ q).trans
        ((hH g hg q hq).trans (le_max_right _ _))
    exact (sourceKPAdelicCompactScalar_height_bound K hζ s q g hq).trans
      (Real.rpow_le_rpow (sourceKPAdelicHeight_pos K hζ g).le hb hr)
  | some x =>
    have he : sourceKPAdelicRationalSummand K hζ
        (sourceKPAdelicPrincipalSeriesScalar K hζ s (sourceKPAdelicCompactSection K hζ s))
        q (sourceKPRationalBorelCosetEquiv K (some x)) =
      sourceKPAdelicCompactScalar K hζ s (sourceKPAdelicProjectiveWeyl K hζ *
        sourceKPAdelicUpperLift K hζ (algebraMap K 𝔸[K] x)*q) := by
      change sourceKPAdelicCompactScalar K hζ s (sourceKPAdelicProjectiveRationalLift K hζ
        (ProjGenLinGroup.mk (sourceGL2Weyl*sourceGL2Upper x))*q) = _
      rw [sourceKPAdelicUpperLift_rational, sourceKPAdelicProjectiveWeyl,
        sourceKPWeylMatrix_field, map_mul, map_mul]
    rw [he]
    exact (sourceKPAdelicCompact_openCell_bound K hζ hs q g hq x).trans
      (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (sourceKPAdelicHeightConstant_pos K hζ g).le
          ((hC g hg).trans (le_max_left _ _)) hr)
        (Real.rpow_nonneg (Height.mulHeight₁_nonneg x) _))

end
end ArtinMatthews
