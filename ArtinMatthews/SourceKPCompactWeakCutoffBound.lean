module

public import ArtinMatthews.SourceKPCompactH1Completion
public import ArtinMatthews.SourceKPCompactTestBumps
public import ArtinMatthews.SourceKPCompactCoreMassNorm
public import ArtinMatthews.SourceKPCompactEnergyRegularity
public import ArtinMatthews.SourceKPCompactH1ClosedForm
public import ArtinMatthews.SourceKPCompactLocalizedIMS
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Compact cutoff energy is controlled by the remaining literal square mass. -/
namespace ArtinMatthews
open NumberField MeasureTheory Filter SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff InnerProductSpace Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "Ω" => productUpper (InfinitePlace K)
local notation "T" => sourceKPCompactC2Core K hζ
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)

theorem sourceKPCompactH1Core_norm_sq_integrals (f : T) :
    ‖sourceKPCompactH1Core K hζ ⟨f⟩‖^2 =
      (∫ y, ‖f.val y‖^2 ∂μY) + ∫ y, sourceKPCompactCoreEnergy K hζ f y ∂μY := by
  rw [sourceKPCompactH1_norm_sq,sourceKPCompactH1Mass_core,sourceKPCompactH1Dirichlet_core,
    sourceKPCompactDirichletCore_self,Complex.ofReal_re]
  exact congrArg (fun x : ℝ => x+∫ y, sourceKPCompactCoreEnergy K hζ f y ∂μY)
    (sourceKPCompactCoreMass_norm_sq K hζ f)

theorem sourceKPCompactWeakCutoff_bound (w d : Y → ℂ) (lam : ℂ) (hw : Continuous w)
    (hwd : ∀ b, ContDiffOn ℝ 2 (sourceKPCompactChartPullback K hζ w b) Ω)
    (hwL : MemLp w 2 μY)
    (hweak : ∀ φ : T, ∃ S : Set Y, IsCompact S ∧ ∀ v : T,
      (∀ y ∈ S, v.val =ᶠ[𝓝 y] w) →
        sourceKPCompactDirichletCore K hζ φ v = ∫ y, star (φ.val y)*(lam*w y-d y) ∂μY)
    (η : T) (hη : ∀ y, (η.val y).im = 0) {M B : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hηM : ∀ y, ‖η.val y‖ ≤ M) (hηB : ∀ y, sourceKPCompactCoreEnergy K hζ η y ≤ B)
    (S : Set Y) (hS : MeasurableSet S) (hd : ∀ y ∉ S, d y = 0)
    (hηS : ∀ y ∈ S, η.val =ᶠ[𝓝 y] 0) :
    ‖sourceKPCompactH1Core K hζ ⟨sourceKPCompactCoreMul K hζ η w hw hwd⟩‖^2 ≤
      (M^2*(1+‖lam‖)+B) * ∫ y in Sᶜ, ‖w y‖^2 ∂μY := by
  let u := sourceKPCompactCoreMul K hζ η w hw hwd
  let R : Y → ℝ := Sᶜ.indicator (fun y => ‖w y‖^2)
  have hRI : Integrable R μY := (hwL.integrable_norm_pow (by norm_num)).indicator hS.compl
  have hη0 (y : Y) (hy : y ∈ S) : η.val y = 0 := (hηS y hy).eq_of_nhds
  have hE0 (y : Y) (hy : y ∈ S) : sourceKPCompactCoreEnergy K hζ η y = 0 :=
    sourceKPCompactCoreEnergy_zero_outside K hζ η (notMem_tsupport_iff_eventuallyEq.mpr (hηS y hy))
  have hRint : (∫ y, R y ∂μY) = ∫ y in Sᶜ, ‖w y‖^2 ∂μY := integral_indicator hS.compl
  have hmass : (∫ y, ‖u.val y‖^2 ∂μY) ≤ M^2 * ∫ y, R y ∂μY := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg (Eventually.of_forall fun y => sq_nonneg _) (hRI.const_mul _)
    apply Eventually.of_forall
    intro y
    change ‖η.val y*w y‖^2 ≤ M^2*R y
    by_cases hy : y ∈ S
    · rw [hη0 y hy,zero_mul,norm_zero,zero_pow (by norm_num),
        show R y = 0 from Set.indicator_of_notMem (by simpa using hy) _,mul_zero]
    · rw [show R y = ‖w y‖^2 from Set.indicator_of_mem hy _,norm_mul,mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hηM y) 2) (sq_nonneg _)
  have hgrad : (∫ y, ‖w y‖^2*sourceKPCompactCoreEnergy K hζ η y ∂μY) ≤
      B*∫ y, R y ∂μY := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg (Eventually.of_forall fun y =>
      mul_nonneg (sq_nonneg _) (sourceKPCompactCoreEnergy_nonneg K hζ η y)) (hRI.const_mul B)
    apply Eventually.of_forall
    intro y
    change ‖w y‖^2*sourceKPCompactCoreEnergy K hζ η y ≤ B*R y
    by_cases hy : y ∈ S
    · rw [hE0 y hy,show R y = 0 from Set.indicator_of_notMem (by simpa using hy) _,mul_zero,mul_zero]
    · rw [show R y = ‖w y‖^2 from Set.indicator_of_mem hy _,mul_comm B]
      exact mul_le_mul_of_nonneg_left (hηB y) (sq_nonneg _)
  have hforce : (∫ y, star ((η.val y)^2*w y)*(lam*w y-d y) ∂μY).re ≤
      (M^2*‖lam‖)*∫ y, R y ∂μY := by
    rw [← integral_const_mul]
    refine (Complex.re_le_norm _).trans (norm_integral_le_of_norm_le (hRI.const_mul _) ?_)
    apply Eventually.of_forall
    intro y
    by_cases hy : y ∈ S
    · rw [hη0 y hy,zero_pow (by norm_num),zero_mul,star_zero,zero_mul,norm_zero,
        show R y = 0 from Set.indicator_of_notMem (by simpa using hy) _,mul_zero]
    · rw [hd y hy,sub_zero,show R y = ‖w y‖^2 from Set.indicator_of_mem hy _,
        norm_mul,norm_star,norm_mul,norm_pow,norm_mul]
      calc
        _ = ‖η.val y‖^2 * (‖lam‖*‖w y‖^2) := by ring
        _ ≤ M^2 * (‖lam‖*‖w y‖^2) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hηM y) 2) (by positivity)
        _ = _ := by ring
  rw [sourceKPCompactH1Core_norm_sq_integrals,
    sourceKPCompactCore_localized_ims K hζ w (fun y => lam*w y-d y) hw hwd hweak η hη,← hRint]
  change (∫ y, ‖u.val y‖^2 ∂μY) +
    ((∫ y, star ((η.val y)^2*w y)*(lam*w y-d y) ∂μY).re +
      ∫ y, ‖w y‖^2*sourceKPCompactCoreEnergy K hζ η y ∂μY) ≤ _
  nlinarith only [hmass,hforce,hgrad]

end
end ArtinMatthews
