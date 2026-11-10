module

public import ArtinMatthews.SourceKPCompactExhaustionCore
public import ArtinMatthews.SourceKPProductHeightExhaustion
public import ArtinMatthews.SourceKPCompactCoreEnergy
public import ArtinMatthews.SourceKPCompactEnergyRegularity
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

namespace ArtinMatthews
open NumberField Matrix SourceHyperbolicGreen Filter
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPCompactExhaustionC2_norm_le_one (n : ℕ)
    (y : SourceKPAutomorphicCompactLevel K hζ) :
    ‖(sourceKPCompactExhaustionC2 K hζ n).val y‖ ≤ 1 := by
  rw [sourceKPCompactExhaustionC2_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sourceKPAutomorphicExhaustionCutoff_nonneg K hζ n y)]
  exact sourceKPAutomorphicExhaustionCutoff_le_one K hζ n y

theorem sourceKPAdelicScalarCutoffProduct_complement_energy_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (T : ℝ), 1 < T → ∀ (q : SourceKPAdelicProjective K hζ)
      (p : ProductSpace (InfinitePlace K)), p ∈ productUpper (InfinitePlace K) →
      productGradientEnergy
        (fun x => (1 : ℂ) - (sourceKPAdelicScalarCutoffProduct K hζ T q x : ℂ)) p ≤
          4 * Fintype.card (InfinitePlace K) * B ^ 2 := by
  obtain ⟨B,hB,hbound⟩ := sourceKPProductHeightExhaustion_energy_bound K hζ
  refine ⟨B,hB,?_⟩
  intro T hT q p hp
  by_cases hlow : ∀ γ : PGL(2,K), sourceKPAdelicProductHeight K hζ
      (sourceKPAdelicProjectiveRationalLift K hζ γ * q) p ≤ 1
  · have he : (fun x => (1 : ℂ) - (sourceKPAdelicScalarCutoffProduct K hζ T q x : ℂ))
        =ᶠ[𝓝 p] fun _ => (1 : ℂ) := by
      filter_upwards [sourceKPAdelicScalarCutoffProduct_eventuallyEq_zero_of_low K hζ hT q p
        (fun v => productUpper_pos hp v) hlow] with x hx
      simp only [hx, Complex.ofReal_zero, sub_zero]
    simp only [productGradientEnergy, productPartial, he.fderiv_eq (𝕜 := ℝ)]
    norm_num [fderiv_const_apply] <;> positivity
  · push_neg at hlow
    obtain ⟨γ,hγ⟩ := hlow
    have he : (fun x => (1 : ℂ) - (sourceKPAdelicScalarCutoffProduct K hζ T q x : ℂ))
        =ᶠ[𝓝 p] fun x =>
          (sourceKPProductHeightExhaustion K hζ
            (sourceKPAdelicProjectiveRationalLift K hζ γ * q) (Real.log T) x : ℂ) := by
      filter_upwards [sourceKPAdelicScalarCutoffProduct_eventuallyEq_of_high K hζ T q γ p
        (fun v => productUpper_pos hp v) hγ] with x hx
      simp only [hx, sourceKPProductHeightExhaustion, Complex.ofReal_sub, Complex.ofReal_one]
    have heE : productGradientEnergy
        (fun x => (1 : ℂ) - (sourceKPAdelicScalarCutoffProduct K hζ T q x : ℂ)) p =
        productGradientEnergy (fun x =>
          (sourceKPProductHeightExhaustion K hζ
            (sourceKPAdelicProjectiveRationalLift K hζ γ * q) (Real.log T) x : ℂ)) p := by
      simp only [productGradientEnergy, productPartial, he.fderiv_eq (𝕜 := ℝ)]
    rw [heE]
    exact hbound _ _ p hp

theorem sourceKPCompactExhaustion_energy_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (y : SourceKPAutomorphicCompactLevel K hζ),
      sourceKPCompactCoreEnergy K hζ (sourceKPCompactExhaustionC2 K hζ n) y ≤ C := by
  obtain ⟨B,hB,hbound⟩ := sourceKPAdelicScalarCutoffProduct_complement_energy_bound K hζ
  refine ⟨4 * Fintype.card (InfinitePlace K) * B ^ 2, by positivity, ?_⟩
  intro n y
  obtain ⟨b,p,rfl⟩ := sourceKPUpperToCompact_cover K hζ y
  rw [sourceKPCompactCoreEnergy_chart]
  obtain ⟨qf,rfl⟩ := Quotient.mk_surjective b
  change productGradientEnergy (sourceKPCompactChartPullback K hζ
    (fun y => (sourceKPAutomorphicExhaustionCutoff K hζ n y : ℂ)) (QuotientGroup.mk qf))
    (sourceKPArchUpperEuclideanMap K p) ≤ _
  have hp : sourceKPArchUpperEuclideanMap K p ∈ productUpper (InfinitePlace K) :=
    fun v _ => SourceArchJacquet.sourceArchUpperEuclideanMap_positive (p v)
  have he := sourceKPAutomorphicExhaustionCutoff_chart_eventuallyEq K hζ n qf _ hp
  have heE : productGradientEnergy (sourceKPCompactChartPullback K hζ
      (fun y => (sourceKPAutomorphicExhaustionCutoff K hζ n y : ℂ)) (QuotientGroup.mk qf))
      (sourceKPArchUpperEuclideanMap K p) =
      productGradientEnergy (fun x => (1 : ℂ) -
        (sourceKPAdelicScalarCutoffProduct K hζ (Real.exp ((n : ℝ) + 1)) (1,qf) x : ℂ))
        (sourceKPArchUpperEuclideanMap K p) := by
    simp only [productGradientEnergy, productPartial, he.fderiv_eq (𝕜 := ℝ)]
  rw [heE]
  exact hbound (Real.exp ((n : ℝ) + 1))
    (Real.one_lt_exp_iff.mpr (by positivity)) (1,qf) _ hp

theorem sourceKPCompactExhaustion_energy_eventually_zero
    (y : SourceKPAutomorphicCompactLevel K hζ) :
    ∀ᶠ n : ℕ in atTop,
      sourceKPCompactCoreEnergy K hζ (sourceKPCompactExhaustionC2 K hζ n) y = 0 := by
  obtain ⟨N,hN⟩ := sourceKPAutomorphicExhaustionCutoff_eventually_locally_one K hζ y
  filter_upwards [eventually_ge_atTop N] with n hn
  obtain ⟨b,p,hpY⟩ := sourceKPUpperToCompact_cover K hζ y
  let x := sourceKPArchUpperEuclideanMap K p
  have hx : x ∈ productUpper (InfinitePlace K) :=
    fun v _ => SourceArchJacquet.sourceArchUpperEuclideanMap_positive (p v)
  let m := fun z => sourceKPUpperToCompact K hζ b (sourceKPArchEuclideanUpperMap K z)
  have hm : ContinuousAt m x :=
    (sourceKPUpperToCompact_continuous K hζ b).continuousAt.comp
      (((sourceKPArchEuclideanUpperMap_continuousOn K) x hx).continuousAt
        ((productUpper_isOpen (InfinitePlace K)).mem_nhds hx))
  have hmx : m x = y := by
    change sourceKPUpperToCompact K hζ b
      (sourceKPArchEuclideanUpperMap K (sourceKPArchUpperEuclideanMap K p)) = y
    rw [sourceKPArchUpperEuclideanMap_left_inverse]
    exact hpY
  have hflat : ∀ᶠ z in 𝓝 x,
      sourceKPAutomorphicExhaustionCutoff K hζ n (m z) = 1 := by
    have ht : Tendsto m (𝓝 x) (𝓝 y) := hmx ▸ hm
    exact (hN n hn).comp_tendsto ht
  have he : sourceKPCompactChartPullback K hζ
      (sourceKPCompactExhaustionC2 K hζ n).val b =ᶠ[𝓝 x] fun _ => (1 : ℂ) := by
    filter_upwards [(productUpper_isOpen (InfinitePlace K)).mem_nhds hx, hflat] with z hz hη
    rw [sourceKPCompactChartPullback, if_pos hz, sourceKPCompactExhaustionC2_apply]
    change (sourceKPAutomorphicExhaustionCutoff K hζ n (m z) : ℂ) = 1
    rw [hη, Complex.ofReal_one]
  rw [← hpY, sourceKPCompactCoreEnergy_chart]
  change productGradientEnergy
    (sourceKPCompactChartPullback K hζ (sourceKPCompactExhaustionC2 K hζ n).val b) x = 0
  simp only [productGradientEnergy, productPartial, he.fderiv_eq (𝕜 := ℝ)]
  norm_num [fderiv_const_apply]

theorem sourceKPCompactExhaustion_complement_tsupport_high (n : ℕ)
    (f : SourceKPAutomorphicCompactLevel K hζ → ℂ) :
    tsupport (fun y => ((1 : ℂ) - (sourceKPCompactExhaustionC2 K hζ (n + 1)).val y) * f y) ⊆
      {y | Real.exp ((n : ℝ) + 1) < sourceKPAutomorphicCompactOrbitHeight K hζ y} := by
  intro y hy
  by_contra hnot
  have hle : sourceKPAutomorphicCompactOrbitHeight K hζ y ≤ Real.exp ((n : ℝ) + 1) :=
    le_of_not_gt hnot
  obtain ⟨c,hc,hcH⟩ := sourceKPAutomorphicCompactOrbitHeight_uniform_pos K hζ
  have hpos : 0 < sourceKPAutomorphicCompactOrbitHeight K hζ y := hc.trans_le (hcH y)
  have hlog := Real.log_le_log hpos hle
  rw [Real.log_exp] at hlog
  have hη : sourceKPAutomorphicExhaustionCutoff K hζ n y = 1 :=
    sourceKPAutomorphicExhaustionCutoff_eq_one K hζ n y hlog
  have hnear : ∀ᶠ z in 𝓝 y, 0 < sourceKPAutomorphicExhaustionCutoff K hζ n z :=
    (sourceKPAutomorphicExhaustionCutoff_continuous K hζ n).continuousAt.eventually_const_lt
      (by rw [hη]; norm_num)
  have hzero : (fun z => ((1 : ℂ) - (sourceKPCompactExhaustionC2 K hζ (n + 1)).val z) * f z)
      =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [hnear] with z hz
    rw [sourceKPCompactExhaustionC2_apply,
      sourceKPAutomorphicExhaustionCutoff_pos_next_eq_one K hζ n z hz,
      Complex.ofReal_one, sub_self, zero_mul]
  exact (notMem_tsupport_iff_eventuallyEq.mpr hzero) hy

end
end ArtinMatthews
