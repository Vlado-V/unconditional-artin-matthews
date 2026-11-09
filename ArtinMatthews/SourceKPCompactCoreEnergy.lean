module

public import ArtinMatthews.SourceKPCompactC2Core
public import ArtinMatthews.SourceKPCompactRationalTransport
public import ArtinMatthews.SourceKPArchProjectiveEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! The actual native Dirichlet density descends to the center-retaining compact-level quotient. -/
namespace ArtinMatthews
open NumberField Matrix Filter SourceHyperbolicGreen SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPCompactChartPullback_rational (f : SourceKPAutomorphicCompactLevel K hζ → ℂ)
    (γ : PGL(2, K)) (b : SourceKPFiniteLevelFiber K hζ)
    (x : ProductSpace (InfinitePlace K)) (hx : x ∈ productUpper (InfinitePlace K)) :
    sourceKPCompactChartPullback K hζ f (γ • b)
      (sourceKPArchEuclideanAction K hζ (sourceKPRationalArchMap K hζ γ) x) =
        sourceKPCompactChartPullback K hζ f b x := by
  rw [sourceKPCompactChartPullback,
    ite_eq_left (sourceKPArchEuclideanAction_positive K hζ (sourceKPRationalArchMap K hζ γ) x),
    sourceKPCompactChartPullback,ite_eq_left hx]
  apply congrArg f
  unfold sourceKPArchEuclideanAction
  rw [sourceKPArchUpperEuclideanMap_left_inverse]
  exact sourceKPUpperToCompact_rational K hζ γ b (sourceKPArchEuclideanUpperMap K x)

theorem sourceKPCompactCoreEnergyLift_rational (f : sourceKPCompactC2Core K hζ)
    (γ : PGL(2, K)) (b : SourceKPFiniteLevelFiber K hζ)
    (x : ProductSpace (InfinitePlace K)) (hx : x ∈ productUpper (InfinitePlace K)) :
    sourceKPCompactCoreEnergyLift K hζ f (γ • b)
      (sourceKPArchEuclideanAction K hζ (sourceKPRationalArchMap K hζ γ) x) =
        sourceKPCompactCoreEnergyLift K hζ f b x := by
  let a := sourceKPRationalArchMap K hζ γ
  let A := sourceKPArchEuclideanAction K hζ a
  let u := sourceKPCompactChartPullback K hζ f.val (γ • b)
  let v := sourceKPCompactChartPullback K hζ f.val b
  have hpos : A x ∈ productUpper (InfinitePlace K) := sourceKPArchEuclideanAction_positive K hζ a x
  have hd : DifferentiableAt ℝ u (A x) :=
    ((f.prop.2.2 (γ • b) (A x) hpos).contDiffAt
      ((productUpper_isOpen (InfinitePlace K)).mem_nhds hpos)).differentiableAt (by norm_num)
  have hmetric : productGradientEnergy (u ∘ A) x = productGradientEnergy u (A x) :=
    sourceKPArchEuclideanAction_gradientEnergy K hζ a u x hx hd
  have he : u ∘ A =ᶠ[𝓝 x] v := by
    filter_upwards [(productUpper_isOpen (InfinitePlace K)).mem_nhds hx] with q hq
    exact sourceKPCompactChartPullback_rational K hζ f.val γ b q hq
  have hsame : productGradientEnergy (u ∘ A) x = productGradientEnergy v x := by
    unfold productGradientEnergy productPartial
    rw [he.fderiv_eq (𝕜 := ℝ)]
  exact hmetric.symm.trans hsame

def sourceKPCompactCoreEnergy (f : sourceKPCompactC2Core K hζ)
    (y : SourceKPAutomorphicCompactLevel K hζ) : ℝ :=
  let b := (sourceKPUpperToCompact_cover K hζ y).choose
  let p := (sourceKPUpperToCompact_cover K hζ y).choose_spec.choose
  sourceKPCompactCoreEnergyLift K hζ f b (sourceKPArchUpperEuclideanMap K p)

theorem sourceKPCompactCoreEnergy_chart (f : sourceKPCompactC2Core K hζ)
    (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K) :
    sourceKPCompactCoreEnergy K hζ f (sourceKPUpperToCompact K hζ b p) =
      sourceKPCompactCoreEnergyLift K hζ f b (sourceKPArchUpperEuclideanMap K p) := by
  let y := sourceKPUpperToCompact K hζ b p
  let c := (sourceKPUpperToCompact_cover K hζ y).choose
  let q := (sourceKPUpperToCompact_cover K hζ y).choose_spec.choose
  have hc : sourceKPUpperToCompact K hζ c q = y :=
    (sourceKPUpperToCompact_cover K hζ y).choose_spec.choose_spec
  obtain ⟨γ,hγ,hq⟩ := (sourceKPUpperToCompact_eq_iff_rational K hζ c b q p).mp hc
  change sourceKPCompactCoreEnergyLift K hζ f c (sourceKPArchUpperEuclideanMap K q) = _
  rw [← hγ,← hq]
  have hp : sourceKPArchUpperEuclideanMap K p ∈ productUpper (InfinitePlace K) :=
    fun i _ => sourceArchUpperEuclideanMap_positive (p i)
  simpa only [sourceKPArchEuclideanAction,sourceKPArchUpperEuclideanMap_left_inverse] using
    sourceKPCompactCoreEnergyLift_rational K hζ f γ b (sourceKPArchUpperEuclideanMap K p) hp

theorem sourceKPCompactCoreEnergy_nonneg (f : sourceKPCompactC2Core K hζ)
    (y : SourceKPAutomorphicCompactLevel K hζ) : 0 ≤ sourceKPCompactCoreEnergy K hζ f y := by
  obtain ⟨b,p,rfl⟩ := sourceKPUpperToCompact_cover K hζ y
  rw [sourceKPCompactCoreEnergy_chart]
  exact sourceKPCompactCoreEnergyLift_nonneg K hζ f b (sourceKPArchUpperEuclideanMap K p)

end
end ArtinMatthews
