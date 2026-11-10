module

public import ArtinMatthews.SourceKPCompactCoreEnergy
public import ArtinMatthews.SourceKPArchHaar
public import ArtinMatthews.SourceKPAutomorphicL2
public import ArtinMatthews.SourceHyperbolicC1Green
public import ArtinMatthews.SourceKPAutomorphicCompactHaar
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The descended native energy is continuous, compactly supported and integrable. -/
namespace ArtinMatthews
open NumberField Matrix Filter MeasureTheory SourceHyperbolicGreen SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPCompactCoreEnergyLift_continuousOn (f : sourceKPCompactC2Core K hζ)
    (b : SourceKPFiniteLevelFiber K hζ) :
    ContinuousOn (sourceKPCompactCoreEnergyLift K hζ f b) (productUpper (InfinitePlace K)) := by
  have hd (i : InfinitePlace K) (j : Fin 3) :
      ContinuousOn (productPartial (sourceKPCompactChartPullback K hζ f.val b) i j)
        (productUpper (InfinitePlace K)) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    exact productPartial_continuousAt_C1
      (((f.prop.2.2 b x hx).contDiffAt ((productUpper_isOpen _).mem_nhds hx)).of_le (by norm_num)) i j
  unfold sourceKPCompactCoreEnergyLift productGradientEnergy
  apply continuousOn_finsetSum
  intro i _
  have hy : ContinuousOn (fun x : ProductSpace (InfinitePlace K) => x i 2)
      (productUpper (InfinitePlace K)) :=
    ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) 2).comp (continuous_apply i)).continuousOn
  apply (hy.pow 2).mul
  apply continuousOn_finsetSum
  intro j _
  exact ((hd i j).norm).pow 2

theorem sourceKPCompactCoreEnergy_chart_continuous (f : sourceKPCompactC2Core K hζ)
    (b : SourceKPFiniteLevelFiber K hζ) :
    Continuous (sourceKPCompactCoreEnergy K hζ f ∘ sourceKPUpperToCompact K hζ b) := by
  have he : sourceKPCompactCoreEnergy K hζ f ∘ sourceKPUpperToCompact K hζ b =
      sourceKPCompactCoreEnergyLift K hζ f b ∘ sourceKPArchUpperEuclideanMap K := by
    funext p
    exact sourceKPCompactCoreEnergy_chart K hζ f b p
  rw [he]
  apply continuous_iff_continuousAt.mpr
  intro p
  have hp : sourceKPArchUpperEuclideanMap K p ∈ productUpper (InfinitePlace K) :=
    fun i _ => sourceArchUpperEuclideanMap_positive (p i)
  exact ((sourceKPCompactCoreEnergyLift_continuousOn K hζ f b _ hp).continuousAt
    ((productUpper_isOpen _).mem_nhds hp)).comp
      (sourceKPArchUpperEuclideanMap_continuous K).continuousAt

theorem sourceKPCompactCoreEnergy_continuous (f : sourceKPCompactC2Core K hζ) :
    Continuous (sourceKPCompactCoreEnergy K hζ f) := by
  apply continuous_def.mpr
  intro V hV
  have he : (sourceKPCompactCoreEnergy K hζ f) ⁻¹' V =
      ⋃ b : SourceKPFiniteLevelFiber K hζ,
        sourceKPUpperToCompact K hζ b ''
          ((sourceKPCompactCoreEnergy K hζ f ∘ sourceKPUpperToCompact K hζ b) ⁻¹' V) := by
    ext y
    constructor
    · intro hy
      obtain ⟨b,p,rfl⟩ := sourceKPUpperToCompact_cover K hζ y
      exact Set.mem_iUnion.mpr ⟨b,p,hy,rfl⟩
    · intro hy
      obtain ⟨b,p,hp,rfl⟩ := Set.mem_iUnion.mp hy
      exact hp
  rw [he]
  apply isOpen_iUnion
  intro b
  exact (sourceKPUpperToCompact_isOpenMap K hζ b) _
    (hV.preimage (sourceKPCompactCoreEnergy_chart_continuous K hζ f b))

omit [NumberField K] in
theorem sourceKPArchEuclideanUpperMap_continuousOn :
    ContinuousOn (sourceKPArchEuclideanUpperMap K) (productUpper (InfinitePlace K)) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have he : (fun p : SourceKPArchPositiveCoordinates K => sourceKPArchEuclideanUpperMap K p.val) =
      sourceKPArchPositiveToUpper K := by
    funext p
    exact (sourceKPArchPositiveToUpper_eq K p).symm
  change Continuous (fun p : SourceKPArchPositiveCoordinates K => sourceKPArchEuclideanUpperMap K p.val)
  rw [he]
  exact sourceKPArchPositiveToUpper_continuous K

theorem sourceKPCompactCoreEnergy_zero_outside (f : sourceKPCompactC2Core K hζ)
    {y : SourceKPAutomorphicCompactLevel K hζ} (hy : y ∉ tsupport f.val) :
    sourceKPCompactCoreEnergy K hζ f y = 0 := by
  obtain ⟨b,p,rfl⟩ := sourceKPUpperToCompact_cover K hζ y
  let x := sourceKPArchUpperEuclideanMap K p
  have hx : x ∈ productUpper (InfinitePlace K) :=
    fun i _ => sourceArchUpperEuclideanMap_positive (p i)
  have hA : ContinuousAt (sourceKPArchEuclideanUpperMap K) x :=
    (sourceKPArchEuclideanUpperMap_continuousOn K _ hx).continuousAt ((productUpper_isOpen _).mem_nhds hx)
  have hg : ContinuousAt (fun q => sourceKPUpperToCompact K hζ b (sourceKPArchEuclideanUpperMap K q)) x :=
    (sourceKPUpperToCompact_continuous K hζ b).continuousAt.comp hA
  have ht : Tendsto (fun q => sourceKPUpperToCompact K hζ b (sourceKPArchEuclideanUpperMap K q))
      (𝓝 x) (𝓝 (sourceKPUpperToCompact K hζ b p)) := by
    simpa only [x,sourceKPArchUpperEuclideanMap_left_inverse] using hg.tendsto
  have hzero : ∀ᶠ q in 𝓝 x,
      f.val (sourceKPUpperToCompact K hζ b (sourceKPArchEuclideanUpperMap K q)) = 0 :=
    ht.eventually (notMem_tsupport_iff_eventuallyEq.mp hy)
  have he : sourceKPCompactChartPullback K hζ f.val b =ᶠ[𝓝 x] (0 : ProductSpace (InfinitePlace K) → ℂ) := by
    filter_upwards [hzero,(productUpper_isOpen _).mem_nhds hx] with q hq hqu
    simpa only [sourceKPCompactChartPullback,ite_eq_left hqu,Pi.zero_apply] using hq
  rw [sourceKPCompactCoreEnergy_chart]
  unfold sourceKPCompactCoreEnergyLift productGradientEnergy productPartial
  rw [he.fderiv_eq (𝕜 := ℝ)]
  simp

theorem sourceKPCompactCoreEnergy_hasCompactSupport (f : sourceKPCompactC2Core K hζ) :
    HasCompactSupport (sourceKPCompactCoreEnergy K hζ f) := by
  apply f.prop.2.1.of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_closure
  intro y hy
  by_contra hnot
  exact hy (sourceKPCompactCoreEnergy_zero_outside K hζ f hnot)

theorem sourceKPCompactCoreEnergy_integrable (f : sourceKPCompactC2Core K hζ) :
    Integrable (sourceKPCompactCoreEnergy K hζ f)
      (sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)) := by
  let : IsFiniteMeasureOnCompacts
      (sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)) :=
    sourceKPAutomorphicCompactHaar_finiteOnCompacts K hζ
  exact (sourceKPCompactCoreEnergy_continuous K hζ f).integrable_of_hasCompactSupport
    (sourceKPCompactCoreEnergy_hasCompactSupport K hζ f)

end
end ArtinMatthews
