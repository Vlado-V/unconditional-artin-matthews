module

public import ArtinMatthews.SourceKPAdelicConstantTermPeriodization
public import ArtinMatthews.SourceKPAdelicUpperTopology
public import ArtinMatthews.SourceKPAdelicHeightCompact


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform rational-periodization bounds on actual compact adelic
sets, for the concrete global intertwining kernel. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicUpperArgument_projection (q : SourceKPAdelicProjective K hζ)
    (g : GL (Fin 2) 𝔸[K]) (hp : sourceKPAdelicProjectiveProjection K hζ q = ProjGenLinGroup.mk g)
    (y : 𝔸[K]) :
    sourceKPAdelicProjectiveProjection K hζ (sourceKPAdelicUpperLift K hζ y*q) =
      ProjGenLinGroup.mk (sourceKPUpperMatrix 𝔸[K] y*g) := by
  rw [map_mul, sourceKPAdelicUpperLift_projection, hp, map_mul]

theorem sourceKPAdelicIntertwiningKernel_compact_bound {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (q : SourceKPAdelicProjective K hζ) (S : Set 𝔸[K]) (hS : IsCompact S) :
    ∃ B : ℝ, 0 < B ∧ ∀ y ∈ S, ∀ x : K,
      ‖sourceKPAdelicIntertwiningKernel K hζ s q (algebraMap K 𝔸[K] x+y)‖ ≤
        B * Height.mulHeight₁ x ^ (-(2*s.re+1)) := by
  obtain ⟨g,hg⟩ := ProjGenLinGroup.mk_surjective (sourceKPAdelicProjectiveProjection K hζ q)
  obtain ⟨C,hC,hbound⟩ := sourceKPAdelicHeightConstant_bounded K hζ
    ((fun y : 𝔸[K] => sourceKPUpperMatrix 𝔸[K] y*g) '' S)
    (sourceKPAdelicUpperRight_isCompact K g S hS)
  have hr : 0 ≤ s.re+1/2 := by
    have hn : 0 ≤ ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  refine ⟨C ^ (s.re+1/2), Real.rpow_pos_of_pos hC _, ?_⟩
  intro y hy x
  rw [sourceKPAdelicIntertwiningKernel_shift]
  apply (sourceKPAdelicCompact_openCell_bound K hζ hs (sourceKPAdelicUpperLift K hζ y*q)
    (sourceKPUpperMatrix 𝔸[K] y*g) (sourceKPAdelicUpperArgument_projection K hζ q g hg.symm y) x).trans
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (sourceKPAdelicHeightConstant_pos K hζ _).le
      (hbound _ ⟨y,hy,rfl⟩) hr) (Real.rpow_nonneg (Height.mulHeight₁_nonneg x) _)

theorem sourceKPAdelicIntertwiningKernel_compact_sum_bound {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (q : SourceKPAdelicProjective K hζ) (S : Set 𝔸[K]) (hS : IsCompact S) :
    ∃ B : ℝ, 0 < B ∧ ∀ y ∈ S,
      (∑' x : K, ‖sourceKPAdelicIntertwiningKernel K hζ s q (algebraMap K 𝔸[K] x+y)‖) ≤
        B * ∑' x : K, Height.mulHeight₁ x ^ (-(2*s.re+1)) := by
  obtain ⟨B,hB,hbound⟩ := sourceKPAdelicIntertwiningKernel_compact_bound K hζ hs q S hS
  refine ⟨B,hB,?_⟩
  intro y hy
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum (hbound y hy)
    (sourceKPAdelicIntertwiningKernel_periodization_summable K hζ hs q y).norm
  exact (sourceKPRationalHeight_rpow_summable K hs).mul_left B

end
end ArtinMatthews
