module

public import ArtinMatthews.SourceThetaBesselTensor


set_option backward.privateInPublic true
@[expose] public section

/-! The constructed analytic tensor is the literal product of the
source03 completed Bessel factors and the supplied finite factors. -/
namespace ArtinMatthews.SourceReflection

open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory
open ArtinMatthews.SourcePhysical
open scoped NumberField Classical ArtinMatthews.SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12) (v : InfinitePlace K)
variable (c : InfinitePlace K → ℝ) (hc : ∀ w, 0 < c w)
variable (m : InfinitePlace K → ℤ) (δ : ℝ) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 5 / 6)
variable (fFinite : ∀ p : S, (p.val.adicCompletion K)ˣ → ℂ)
variable (hFinite : ∀ p, Continuous (fFinite p)) (n : S → ℤ) (B : S → ℝ) (hB : ∀ p, 0 ≤ B p)
variable (hSupport : ∀ (p : S) (z : (p.val.adicCompletion K)ˣ),
  z ∉ sourceLocalMulBall K p.val (n p) → fFinite p z = 0)
variable (hSmall : ∀ (p : S) (z : (p.val.adicCompletion K)ˣ), z ∈ sourceLocalMulBall K p.val 0 →
  ‖fFinite p z‖ ≤ B p * (sourceSheetFiniteNorm S p z) ^ δ)

local notation "D" => sourceThetaBesselTensor K S hζ v c hc m δ hδ hδ₁ fFinite hFinite n B hB hSupport hSmall

theorem sourceThetaBesselTensor_literal (x : SWholeUnits K S) :
    sourceThetaSLocalTensor K S hζ v ((D).localDeriv 0) (D).retained x =
      (∏ w, sourceThetaBesselCompletedFactor K hζ w (c w) (m w) (x.1 w)) *
        ∏ p, fFinite p (x.2 p) := by
  change sourceThetaBesselAngularLogDerivative (c v) (m v) 0
      (sourceComplexUnitAngle (sourceComplexPlaceUnitsEquiv (sourceSLocalComplexPlace K hζ v) (x.1 v)))
      (sourceComplexUnitLogNorm (sourceComplexPlaceUnitsEquiv (sourceSLocalComplexPlace K hζ v) (x.1 v))) *
      ((∏ w : {w : InfinitePlace K // w ≠ v},
        sourceThetaBesselCompletedFactor K hζ w.val (c w.val) (m w.val) (x.1 w.val)) *
          ∏ p, fFinite p (x.2 p)) = _
  rw [← sourceThetaBesselComplexFactor_eq_log (hc v)]
  change sourceThetaBesselCompletedFactor K hζ v (c v) (m v) (x.1 v) * _ = _
  rw [Fintype.prod_eq_mul_prod_subtype_ne (fun w : InfinitePlace K =>
    sourceThetaBesselCompletedFactor K hζ w (c w) (m w) (x.1 w)) v, mul_assoc]

end
end ArtinMatthews.SourceReflection
