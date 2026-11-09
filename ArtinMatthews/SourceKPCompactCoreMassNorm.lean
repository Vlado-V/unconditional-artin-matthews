module

public import ArtinMatthews.SourceKPCompactCoreMass


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField MeasureTheory
open scoped NumberField MatrixGroups AdeleRing ContDiff
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPCompactCore_norm_sq_integrable {n : ℕ∞ω} (f : sourceKPCompactCore K hζ n) :
    Integrable (fun y => ‖f.val y‖ ^ 2)
      (sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)) :=
  (sourceKPCompactCore_memLp K hζ f).integrable_norm_pow (by norm_num)

theorem sourceKPCompactCoreMass_norm_sq {n : ℕ∞ω} (f : sourceKPCompactCore K hζ n) :
    ‖sourceKPCompactCoreMass K hζ n f‖ ^ 2 =
      ∫ y, ‖f.val y‖ ^ 2 ∂sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ) := by
  have he : inner ℂ (sourceKPCompactCoreMass K hζ n f) (sourceKPCompactCoreMass K hζ n f) =
      ((∫ y, ‖f.val y‖ ^ 2 ∂sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ) : ℝ) : ℂ) := by
    rw [L2.inner_def, ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [sourceKPCompactCoreMass_coe K hζ f] with y hy
    rw [hy, inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow]
  rw [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow] at he
  exact Complex.ofReal_injective he

end
end ArtinMatthews
