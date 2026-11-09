module

public import ArtinMatthews.SourceKPAdelicCutoffGenuine
public import ArtinMatthews.SourceKPAdelicCutoffDefect


set_option backward.privateInPublic true
@[expose] public section

/-! The literal Casimir and the compact cutoff defect preserve the
actual cubic central character. -/

namespace ArtinMatthews
open NumberField
open scoped NumberField BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceArchGlobalCasimir_left_covariant
    (f : SourceKPAdelicProjective K hζ → ℂ) (a : SourceKPAdelicProjective K hζ) (c : ℂ)
    (hf : ∀ q, f (a*q) = c*f q) (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K) :
    sourceArchGlobalCasimir K hζ f (a*q) v = c*sourceArchGlobalCasimir K hζ f q v := by
  have hU (z : ℂ) : sourceArchGlobalUpperTranslate K hζ f (a*q) v z =
      fun t => c*sourceArchGlobalUpperTranslate K hζ f q v z t := by
    funext t
    unfold sourceArchGlobalUpperTranslate
    rw [mul_assoc,hf]
  have hA : sourceArchGlobalDiagonalTranslate K hζ f (a*q) v =
      fun t => c*sourceArchGlobalDiagonalTranslate K hζ f q v t := by
    funext t
    unfold sourceArchGlobalDiagonalTranslate
    rw [mul_assoc,hf]
  unfold sourceArchGlobalCasimir
  rw [hU 1,hU Complex.I,hA]
  simp only [deriv_const_mul_field',deriv_const_mul_field]
  ring

theorem sourceKPAdelicCutoffCasimir_center (T : ℝ) (s : ℂ) (z : rootsOfUnity 3 K)
    (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K) :
    sourceArchGlobalCasimir K hζ (sourceKPAdelicCutoffEisenstein K hζ T s)
      (sourceKPAdelicProjectiveCenter K hζ z*q) v =
        (sourceKPAdelicCentralComplex K hζ z : ℂ) *
          sourceArchGlobalCasimir K hζ (sourceKPAdelicCutoffEisenstein K hζ T s) q v :=
  sourceArchGlobalCasimir_left_covariant K hζ _ _ _
    (sourceKPAdelicCutoffEisenstein_center K hζ T s z) q v

theorem sourceKPAdelicCutoffCasimirDefect_center (T : ℝ) (s : ℂ) (z : rootsOfUnity 3 K)
    (q : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicCutoffCasimirDefect K hζ T s (sourceKPAdelicProjectiveCenter K hζ z*q) =
      (sourceKPAdelicCentralComplex K hζ z : ℂ)*sourceKPAdelicCutoffCasimirDefect K hζ T s q := by
  unfold sourceKPAdelicCutoffCasimirDefect
  simp_rw [sourceKPAdelicCutoffCasimir_center,sourceKPAdelicCutoffEisenstein_center]
  rw [← Finset.mul_sum]
  ring

end
end ArtinMatthews
