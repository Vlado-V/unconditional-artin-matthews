module

public import ArtinMatthews.SourceEisensteinNonconstant


set_option backward.privateInPublic true
@[expose] public section

/-! The actual compact and unipotent periods are retained by the nonconstant cusp remainder. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicCompactEisenstein_deepCompact_right (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (k : sourceKPAdelicDeepCompact K hζ) :
    sourceKPAdelicCompactEisenstein K hζ s (g * k.val) = sourceKPAdelicCompactEisenstein K hζ s g := by
  unfold sourceKPAdelicCompactEisenstein sourceKPAdelicEisensteinSum
  apply tsum_congr
  intro c
  induction c using Quotient.inductionOn with
  | _ γ =>
    change sourceKPAdelicCompactScalar K hζ s (sourceKPAdelicProjectiveRationalLift K hζ γ * (g * k.val)) =
      sourceKPAdelicCompactScalar K hζ s (sourceKPAdelicProjectiveRationalLift K hζ γ * g)
    rw [← mul_assoc]
    exact sourceKPAdelicCompactScalar_right K hζ s _ k

theorem sourceKPAdelicTraceIntertwiner_deepCompact_right (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (k : sourceKPAdelicDeepCompact K hζ) :
    sourceKPAdelicTraceIntertwiner K hζ s (g * k.val) = sourceKPAdelicTraceIntertwiner K hζ s g := by
  unfold sourceKPAdelicTraceIntertwiner sourceKPAdelicIntertwiner
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  unfold sourceKPAdelicIntertwiningKernel
  rw [← mul_assoc]
  exact sourceKPAdelicCompactScalar_right K hζ s _ k

theorem sourceKPAdelicNonconstantEisenstein_deepCompact_right (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (k : sourceKPAdelicDeepCompact K hζ) :
    sourceKPAdelicNonconstantEisenstein K hζ s (g * k.val) = sourceKPAdelicNonconstantEisenstein K hζ s g := by
  rw [sourceKPAdelicNonconstantEisenstein, sourceKPAdelicNonconstantEisenstein,
    sourceKPAdelicCompactEisenstein_deepCompact_right, sourceKPAdelicCompactScalar_right,
    sourceKPAdelicTraceIntertwiner_deepCompact_right]

theorem sourceKPAdelicNonconstantEisenstein_upper_rational {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1)
    (g : SourceKPAdelicProjective K hζ) (y : 𝔸[K]) (a : K) :
    sourceKPAdelicNonconstantEisenstein K hζ s
      (sourceKPAdelicUpperLift K hζ (algebraMap K 𝔸[K] a + y) * g) =
        sourceKPAdelicNonconstantEisenstein K hζ s (sourceKPAdelicUpperLift K hζ y * g) := by
  rw [sourceKPAdelicNonconstantEisenstein_upper, sourceKPAdelicNonconstantEisenstein_upper,
    sourceKPAdelicCompactEisenstein_upper_rational K hζ hs g y a]

end
end ArtinMatthews
