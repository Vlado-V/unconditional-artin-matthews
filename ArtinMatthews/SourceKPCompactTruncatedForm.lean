module

public import ArtinMatthews.SourceKPAutomorphicDefectL2
public import ArtinMatthews.SourceKPAutomorphicCompactTruncated
public import ArtinMatthews.SourceKPCompactH1Completion
public import ArtinMatthews.SourceKPAdelicEisensteinProductC2
public import ArtinMatthews.SourceKPCompactEisensteinContinuity
public import ArtinMatthews.SourceKPCompactH1WeakTests
public import ArtinMatthews.SourceKPCompactTruncatedChart
public import ArtinMatthews.SourceKPCompactWeakExhaustionRealization
public import ArtinMatthews.SourceKPCompactWeakTestGlue
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

/-! The literal initial truncated series is realized by the actual closed form. -/
namespace ArtinMatthews
open NumberField MeasureTheory Filter SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff InnerProductSpace Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "V" => SourceKPCompactH1 K hζ
local notation "j₀" => sourceKPCompactH1Mass K hζ
local notation "L" => SourceKPAutomorphicL2 K hζ (sourceKPArchHaar K hζ)
local notation "Ω" => productUpper (InfinitePlace K)

theorem sourceKPCompactChartPullback_truncated_C2 {T : ℝ} (hT : 0 < T) {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (b : SourceKPFiniteLevelFiber K hζ) :
    ContDiffOn ℝ 2 (sourceKPCompactChartPullback K hζ
      (sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s) b) Ω := by
  obtain ⟨qf,rfl⟩ := Quotient.mk_surjective b
  change ContDiffOn ℝ 2 (sourceKPCompactChartPullback K hζ
    (sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s) (QuotientGroup.mk qf)) Ω
  rw [sourceKPCompactChartPullback_truncated]
  apply (sourceKPAdelicEisensteinProductChart_contDiffOn_two K hζ hs (1,qf)).sub
  intro p hp
  exact ((sourceKPAdelicCutoffEisensteinProductChart_contDiffAt K hζ hT s (1,qf) p
    (fun v => productUpper_pos hp v)).of_le (by simp)).contDiffWithinAt

private theorem sourceKPCompactCoreMass_inner_of_ae (φ : sourceKPCompactC2Core K hζ)
    (f : L) (g : Y → ℂ) (hf : (f : Y → ℂ) =ᵐ[μY] g) :
    inner ℂ (sourceKPCompactCoreMass K hζ 2 φ) f =
      ∫ y, star (φ.val y)*g y ∂μY := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sourceKPCompactCoreMass_coe K hζ φ,hf] with y hy hy'
  rw [hy,hy',RCLike.inner_apply']
  rfl

theorem sourceKPCompactTruncated_form {T : ℝ} (hT : 1 ≤ T) {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (hwL : MemLp (sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s) 2 μY) :
    ∃ u : V,
      (j₀ u : Y → ℂ) =ᵐ[μY] sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s ∧
      ∀ v : V, sourceKPCompactH1Dirichlet K hζ v u =
        (InfinitePlace.nrComplexPlaces K : ℂ)*(1-4*s^2) * inner ℂ (j₀ v) (j₀ u) -
          inner ℂ (j₀ v) (sourceKPAutomorphicDefectL2 K hζ hT s) := by
  let ht : 0 < T := lt_of_lt_of_le zero_lt_one hT
  let w := sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s
  let d := sourceKPAutomorphicCompactCutoffDefect K hζ ht s
  let lam : ℂ := (InfinitePlace.nrComplexPlaces K : ℂ)*(1-4*s^2)
  have hw : Continuous w := sourceKPAutomorphicCompactTruncatedEisenstein_continuous K hζ ht hs
  have hd : Continuous d := by
    have hm : Continuous (fun x : Y => (s,x)) := continuous_const.prodMk continuous_id
    simpa only [Function.comp_def] using
      (sourceKPAutomorphicCompactCutoffDefect_joint_continuous K hζ ht).comp hm
  have hd0 (y : Y) (hy : 2*T < sourceKPAutomorphicCompactOrbitHeight K hζ y) : d y = 0 := by
    by_contra hn
    exact (not_le_of_gt hy) (sourceKPAutomorphicCompactCutoffDefect_support K hζ hT s hn)
  have hweak (φ : sourceKPCompactC2Core K hζ) : ∃ S : Set Y, IsCompact S ∧
      ∀ v : sourceKPCompactC2Core K hζ, (∀ y ∈ S, v.val =ᶠ[𝓝 y] w) →
        sourceKPCompactDirichletCore K hζ φ v =
          ∫ y, star (φ.val y)*(lam*w y-d y) ∂μY := by
    obtain ⟨S,hS,h⟩ := sourceKPCompactTruncated_weak_localization K hζ ht hs φ
    refine ⟨S,hS,fun v hv => (h v hv).trans ?_⟩
    rw [← integral_const_mul,← integral_sub
      ((sourceKPCompactCore_test_pair_integrable K hζ φ w hw).const_mul lam)
      (sourceKPCompactCore_test_pair_integrable K hζ φ d hd)]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by ring
  obtain ⟨u,hu,h⟩ := sourceKPCompactWeakExhaustion_realization K hζ w d lam hw
    (sourceKPCompactChartPullback_truncated_C2 K hζ ht hs) hwL (2*T) hd0 hweak
  let dL := sourceKPAutomorphicDefectL2 K hζ hT s
  refine ⟨u,hu,?_⟩
  intro v
  have hcore (φ : sourceKPCompactC2Core K hζ) :
      sourceKPCompactH1Dirichlet K hζ (sourceKPCompactH1Core K hζ ⟨φ⟩) u =
        lam * inner ℂ (sourceKPCompactCoreMass K hζ 2 φ) (j₀ u) +
          inner ℂ (sourceKPCompactCoreMass K hζ 2 φ) (-dL) := by
    rw [inner_neg_right,sourceKPCompactCoreMass_inner_of_ae K hζ φ (j₀ u) w hu,
      sourceKPCompactCoreMass_inner_of_ae K hζ φ dL d (sourceKPAutomorphicDefectL2_ae K hζ hT s)]
    calc
      _ = ∫ y, star (φ.val y)*(lam*w y-d y) ∂μY := h φ
      _ = _ := by
        rw [← integral_const_mul,← sub_eq_add_neg,← integral_sub
          ((sourceKPCompactCore_test_pair_integrable K hζ φ w hw).const_mul lam)
          (sourceKPCompactCore_test_pair_integrable K hζ φ d hd)]
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by ring
  simpa only [lam,dL,inner_neg_right,sub_eq_add_neg] using
    sourceKPCompactH1_weak_of_core K hζ u (-dL) lam hcore v

end
end ArtinMatthews
