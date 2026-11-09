module

public import ArtinMatthews.SourceKPCompactTestBumps
public import ArtinMatthews.SourceKPCompactCorePairChart
public import ArtinMatthews.SourceHyperbolicProductIMS


set_option backward.privateInPublic true
@[expose] public section

/-! The exact real multiplier identity on the actual automorphic core. -/

namespace ArtinMatthews
open NumberField MeasureTheory Filter SourceHyperbolicGreen SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff InnerProductSpace Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "P" => ProductSpace (InfinitePlace K)
local notation "Ω" => productUpper (InfinitePlace K)
local notation "T" => sourceKPCompactC2Core K hζ
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)

def sourceKPCompactCoreProduct (φ ψ : T) : T :=
  sourceKPCompactCoreMul K hζ φ ψ.val ψ.prop.1 ψ.prop.2.2

theorem sourceKPCompactCoreProduct_val (φ ψ : T) :
    (sourceKPCompactCoreProduct K hζ φ ψ).val = φ.val*ψ.val := rfl

theorem sourceKPCompactCoreEnergy_sub_le (f g : T) (y : Y) :
    sourceKPCompactCoreEnergy K hζ (f-g) y ≤
      2*(sourceKPCompactCoreEnergy K hζ f y+sourceKPCompactCoreEnergy K hζ g y) := by
  let A := sourceKPCompactCoreGradientAtLinear K hζ y
  have he (u : T) : sourceKPCompactCoreEnergy K hζ u y = ‖A u‖^2 :=
    (sourceKPCompactCoreGradientAt_norm_sq K hζ u y).symm
  rw [he,he,he,map_sub]
  exact (pow_le_pow_left₀ (norm_nonneg (A f-A g)) (norm_sub_le (A f) (A g)) 2).trans
    (by nlinarith [sq_nonneg (‖A f‖-‖A g‖)])

theorem sourceKPCompactCoreEnergy_mul_ims (η v : T) (hη : ∀ y, (η.val y).im = 0) (y : Y) :
    sourceKPCompactCoreEnergy K hζ (sourceKPCompactCoreProduct K hζ η v) y =
      (sourceKPCompactCorePairDensity K hζ
        (sourceKPCompactCoreProduct K hζ (sourceKPCompactCoreProduct K hζ η η) v) v y).re +
      ‖v.val y‖^2*sourceKPCompactCoreEnergy K hζ η y := by
  obtain ⟨b,p,rfl⟩ := sourceKPUpperToCompact_cover K hζ y
  let x := sourceKPArchUpperEuclideanMap K p
  have hx : x ∈ Ω := fun i _ => sourceArchUpperEuclideanMap_positive (p i)
  let G := sourceKPCompactChartPullback K hζ η.val b
  let W := sourceKPCompactChartPullback K hζ v.val b
  let E : P → ℝ := fun q => (G q).re
  have hE : (fun q => (E q : ℂ)) = G := by
    funext q
    apply Complex.ext
    · exact Complex.ofReal_re _
    · rw [Complex.ofReal_im]
      dsimp only [G]
      by_cases hq : q ∈ Ω
      · simp only [sourceKPCompactChartPullback,ite_eq_left hq]
        exact (hη _).symm
      · simp [sourceKPCompactChartPullback,hq]
  have hdG := ((η.prop.2.2 b x hx).contDiffAt ((productUpper_isOpen _).mem_nhds hx)).differentiableAt
    (by norm_num)
  have hdE : DifferentiableAt ℝ E x := Complex.reCLM.differentiableAt.comp x hdG
  have hdW : DifferentiableAt ℝ W x :=
    ((v.prop.2.2 b x hx).contDiffAt ((productUpper_isOpen _).mem_nhds hx)).differentiableAt (by norm_num)
  have h := productGradientEnergy_real_mul_ims hdE hdW
  have hW : W x = v.val (sourceKPUpperToCompact K hζ b p) := by
    dsimp only [W]
    rw [sourceKPCompactChartPullback,ite_eq_left hx,sourceKPArchUpperEuclideanMap_left_inverse]
  rw [sourceKPCompactCoreEnergy_chart,sourceKPCompactCorePairDensity_chart,
    sourceKPCompactCoreEnergy_chart]
  simp only [sourceKPCompactCoreEnergyLift,sourceKPCompactCoreProduct_val,sourceKPCompactChartPullback_mul]
  change productGradientEnergy (G*W) x =
    (productGradientPair ((G*G)*W) W x).re + ‖v.val (sourceKPUpperToCompact K hζ b p)‖^2*
      productGradientEnergy G x
  rw [← hW,← hE]
  simpa only [Pi.mul_def,pow_two] using h

end
end ArtinMatthews
