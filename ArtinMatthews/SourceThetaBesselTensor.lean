module

public import ArtinMatthews.SourceThetaBesselCompleted


set_option backward.privateInPublic true
@[expose] public section

/-! A concrete source03 Bessel tensor has all the local analytic input
required by the exact sheet and reflected-profile theorems. -/
namespace ArtinMatthews.SourceReflection

open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory
open ArtinMatthews.SourcePhysical
open scoped NumberField Classical ArtinMatthews.SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12) (v : InfinitePlace K)

def sourceThetaBesselTensor (c : InfinitePlace K → ℝ) (hc : ∀ w, 0 < c w)
    (m : InfinitePlace K → ℤ) (δ : ℝ) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 5 / 6)
    (fFinite : ∀ p : S, (p.val.adicCompletion K)ˣ → ℂ)
    (hFinite : ∀ p, Continuous (fFinite p)) (n : S → ℤ) (B : S → ℝ) (hB : ∀ p, 0 ≤ B p)
    (hSupport : ∀ (p : S) (z : (p.val.adicCompletion K)ˣ),
      z ∉ sourceLocalMulBall K p.val (n p) → fFinite p z = 0)
    (hSmall : ∀ (p : S) (z : (p.val.adicCompletion K)ˣ), z ∈ sourceLocalMulBall K p.val 0 →
      ‖fFinite p z‖ ≤ B p * (sourceSheetFiniteNorm S p z) ^ δ) :
    SourceThetaRotatedTensor K S hζ v δ :=
  SourceThetaRotatedTensor.ofLocal K S hζ v δ
    (sourceThetaBesselAngularLogDerivative (c v) (m v))
    (sourceThetaBesselAngularLogDerivative_measurable (hc v) (m v))
    (sourceThetaBesselAngularLogDerivative_hasDerivAt (hc v) (m v))
    (fun j _A hA => sourceThetaBesselAngularLogDerivative_twoEnded_of_le (hc v) (m v) j hδ hδ₁ hA.le)
    (fun w => sourceThetaBesselCompletedFactor K hζ w (c w) (m w))
    (fun w => sourceThetaBesselCompletedFactor_measurable K hζ w.val (hc w.val) (m w.val))
    (fun w _A hA => sourceThetaBesselCompletedFactor_twoEnded_of_le K hζ w.val
      (hc w.val) (m w.val) hδ hδ₁ hA.le)
    fFinite hFinite n B hB hSupport hSmall

end
end ArtinMatthews.SourceReflection
