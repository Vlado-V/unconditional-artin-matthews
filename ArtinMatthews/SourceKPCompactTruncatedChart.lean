module

public import ArtinMatthews.SourceKPAdelicCutoffProductChart
public import ArtinMatthews.SourceKPAdelicProductCoordinatePaths
public import ArtinMatthews.SourceKPAdelicRationalProductChart
public import ArtinMatthews.SourceKPAutomorphicCompactTruncated
public import ArtinMatthews.SourceKPCompactC2Core
public import ArtinMatthews.SourceKPAdelicCutoffProductDefect
public import ArtinMatthews.SourceKPAdelicEisensteinProductC1
public import ArtinMatthews.SourceKPCompactEisensteinChart
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

/-! Exact product-coordinate pullbacks of the actual truncated series. -/

namespace ArtinMatthews
open NumberField Matrix OAI.CubicEisenstein SourceArchJacquet SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "P" => ProductSpace (InfinitePlace K)
local notation "Ω" => productUpper (InfinitePlace K)
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ

theorem sourceKPCompactChartPullback_of_positive (f : Y → ℂ) (b : SourceKPFiniteLevelFiber K hζ)
    (p : P) (hp : p ∈ Ω) :
    sourceKPCompactChartPullback K hζ f b p =
      f (sourceKPUpperToCompact K hζ b (sourceKPArchEuclideanUpperMap K p)) :=
  ite_eq_left hp

theorem sourceKPCompactChartPullback_of_not_positive (f : Y → ℂ)
    (b : SourceKPFiniteLevelFiber K hζ) (p : P) (hp : p ∉ Ω) :
    sourceKPCompactChartPullback K hζ f b p = 0 :=
  ite_eq_right hp

theorem sourceKPUpperToCompact_product_point
    (qf : SourceKPFiniteAdeleProjective K hζ) (p : P) (hp : p ∈ Ω) :
    sourceKPUpperToCompact K hζ (QuotientGroup.mk qf) (sourceKPArchEuclideanUpperMap K p) =
      sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ
        ((1,qf)*sourceKPAdelicUpperProductPoint K hζ p (fun v => productUpper_pos hp v))) := by
  let x := sourceKPArchEuclideanUpperMap K p
  have he : sourceKPArchUpperEuclideanMap K x = p :=
    sourceKPArchUpperEuclideanMap_right_inverse K p (fun v => productUpper_pos hp v)
  have hm : sourceKPArchUpperHalfSection K hζ x =
      sourceArchUpperHalfspaceMatrix K hζ p (fun v => productUpper_pos hp v) := by
    rw [← sourceKPArchUpperHalfspaceMatrix_euclidean]
    simp only [he]
  rw [sourceKPUpperToCompact_section,hm]
  congr 2
  exact Prod.ext (one_mul _).symm (mul_one _).symm

theorem sourceKPCompactChartPullback_eisenstein (s : ℂ)
    (qf : SourceKPFiniteAdeleProjective K hζ) :
    sourceKPCompactChartPullback K hζ (sourceKPAutomorphicCompactEisenstein K hζ s)
      (QuotientGroup.mk qf) =
      sourceKPAdelicEisensteinProductChart K hζ s (1,qf) := by
  funext p
  by_cases hp : p ∈ Ω
  · calc
      _ = sourceKPAutomorphicCompactEisenstein K hζ s
          (sourceKPUpperToCompact K hζ (QuotientGroup.mk qf) (sourceKPArchEuclideanUpperMap K p)) :=
        sourceKPCompactChartPullback_of_positive K hζ _ (QuotientGroup.mk qf) p hp
      _ = _ := by
        rw [sourceKPUpperToCompact_product_point K hζ qf p hp,
          sourceKPAutomorphicCompactEisenstein_adelic,sourceKPAdelicEisensteinProductChart,
          dite_eq_left (fun v => productUpper_pos hp v)] <;> rfl
  · have hn : ¬∀ v, 0 < p v 2 := fun h => hp (fun v _ => h v)
    exact (sourceKPCompactChartPullback_of_not_positive K hζ _ (QuotientGroup.mk qf) p hp).trans
      (by rw [sourceKPAdelicEisensteinProductChart,dite_eq_right hn])

theorem sourceKPCompactChartPullback_cutoff (T : ℝ) (s : ℂ)
    (qf : SourceKPFiniteAdeleProjective K hζ) :
    sourceKPCompactChartPullback K hζ (sourceKPAutomorphicCompactCutoffEisenstein K hζ T s)
      (QuotientGroup.mk qf) =
      sourceKPAdelicCutoffEisensteinProductChart K hζ T s (1,qf) := by
  funext p
  by_cases hp : p ∈ Ω
  · calc
      _ = sourceKPAutomorphicCompactCutoffEisenstein K hζ T s
          (sourceKPUpperToCompact K hζ (QuotientGroup.mk qf) (sourceKPArchEuclideanUpperMap K p)) :=
        sourceKPCompactChartPullback_of_positive K hζ _ (QuotientGroup.mk qf) p hp
      _ = _ := by
        rw [sourceKPUpperToCompact_product_point K hζ qf p hp]
        exact (sourceKPAdelicCutoffEisensteinProductChart_compact_value K hζ T s (1,qf) p
          (fun v => productUpper_pos hp v)).symm
  · have hn : ¬∀ v, 0 < p v 2 := fun h => hp (fun v _ => h v)
    exact (sourceKPCompactChartPullback_of_not_positive K hζ _ (QuotientGroup.mk qf) p hp).trans
      (by rw [sourceKPAdelicCutoffEisensteinProductChart,dite_eq_right hn])

theorem sourceKPCompactChartPullback_sub (f g : Y → ℂ) (b : SourceKPFiniteLevelFiber K hζ) :
    sourceKPCompactChartPullback K hζ (f-g) b =
      sourceKPCompactChartPullback K hζ f b-sourceKPCompactChartPullback K hζ g b := by
  funext p
  by_cases hp : p ∈ Ω <;> simp [sourceKPCompactChartPullback,hp]

theorem sourceKPCompactChartPullback_truncated (T : ℝ) (s : ℂ)
    (qf : SourceKPFiniteAdeleProjective K hζ) :
    sourceKPCompactChartPullback K hζ (sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s)
      (QuotientGroup.mk qf) =
      sourceKPAdelicEisensteinProductChart K hζ s (1,qf) -
      sourceKPAdelicCutoffEisensteinProductChart K hζ T s (1,qf) := by
  exact (sourceKPCompactChartPullback_sub K hζ
    (sourceKPAutomorphicCompactEisenstein K hζ s)
    (sourceKPAutomorphicCompactCutoffEisenstein K hζ T s) (QuotientGroup.mk qf)).trans
      (congrArg₂ (·-·) (sourceKPCompactChartPullback_eisenstein K hζ s qf)
        (sourceKPCompactChartPullback_cutoff K hζ T s qf))

theorem sourceKPCompactChartPullback_continuousOn (f : Y → ℂ) (hf : Continuous f)
    (b : SourceKPFiniteLevelFiber K hζ) :
    ContinuousOn (sourceKPCompactChartPullback K hζ f b) Ω := by
  apply (hf.comp_continuousOn ((sourceKPUpperToCompact_continuous K hζ b).comp_continuousOn
    (sourceKPArchEuclideanUpperMap_continuousOn K))).congr
  intro p hp
  exact sourceKPCompactChartPullback_of_positive K hζ f b p hp

theorem sourceKPCompactChartPullback_truncated_C1 {T : ℝ} (hT : 0 < T) {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (b : SourceKPFiniteLevelFiber K hζ) :
    ContDiffOn ℝ 1 (sourceKPCompactChartPullback K hζ
      (sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s) b) Ω := by
  obtain ⟨qf,rfl⟩ := Quotient.mk_surjective b
  change ContDiffOn ℝ 1 (sourceKPCompactChartPullback K hζ
    (sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s) (QuotientGroup.mk qf)) Ω
  rw [sourceKPCompactChartPullback_truncated]
  apply (sourceKPAdelicEisensteinProductChart_contDiffOn K hζ hs (1,qf)).sub
  intro p hp
  exact ((sourceKPAdelicCutoffEisensteinProductChart_contDiffAt K hζ hT s (1,qf) p
    (fun v => productUpper_pos hp v)).of_le (by simp)).contDiffWithinAt

end
end ArtinMatthews
