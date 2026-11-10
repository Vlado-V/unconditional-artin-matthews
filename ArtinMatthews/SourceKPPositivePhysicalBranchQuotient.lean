module

public import ArtinMatthews.SourceKPPhysicalBranch
public import ArtinMatthews.SourceFrequencyPoissonArgument
public import ArtinMatthews.SourceKPPositivePhysicalBranchBounds
public import ArtinMatthews.SourceKPPositiveQuotientSeries
public import ArtinMatthews.SourcePrimeNormSummability
public import ArtinMatthews.SourceThetaGaussianMoments
public import ArtinMatthews.SourceThetaPositiveSheetBounds
public import ArtinMatthews.SourceThetaSmoothingSum
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

/-! Each literal positive branch has finite sheet mass and an absolutely
integrable Gaussian convolution on the genuine norm-one quotient. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain QuadraticWeil MeasureTheory
open VaryingKummerAnalytic SourcePhysical SourceReflection AllowedGenerators
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 12) (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "Whole" => SWholeUnits K S
local notation "E" => SourcePrimeExponents K S₀
local notation "C" => ReflectionSquarefreeExponents K S₀
local notation "PE" => SourceExteriorPrime K S₀
local notation "D" => sWholeDiagonal K S
local notation "Γ" => sNormOneSixthSubgroup K S
local notation "bessel" => (fun _ : InfinitePlace K => 4 * Real.pi)
local notation "N" => sourcePrimeExponentNorm K S₀

private theorem positiveBranchExponents_countable : Countable E := by
  let f (e : E) := (N e : ℝ) ^ (-2 : ℝ)
  have hs : Summable f := sourcePrimeExponentNorm_summable K S₀ (σ := 2) (by norm_num)
  have hf : Function.support f = Set.univ := Set.eq_univ_of_forall fun e =>
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos K S₀ e)) _).ne'
  exact Set.countable_univ_iff.mp (hf ▸ hs.countable_support)

variable {J : Ideal (𝓞 K)}
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (hcut : principalAngularCutoff K J ⊆ sourceHilbertSet K S₀) (v : InfinitePlace K)
    {T : ℝ} (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)

include hS hJ hcut hT

local notation "ν" => sourceSLocalNormalizedSheetMeasure K hζ S v
local notation "B[" e "," u "," g "]" =>
  sourceKPPositivePhysicalBranchValue K hζ S₀ hS η hJ hT p e u g
local notation "hB[" e "," u "," g "]" =>
  sourceKPPositivePhysicalBranchValue_invariant K hζ S₀ hS η hJ hcut hT p e u g
local notation "P[" e "," u "," g "]" =>
  sourceSLocalQuotientSheetProfile S hζ ν B[e,u,g] hB[e,u,g]
local notation "A" => sourceKPPositivePhysicalBranchAmplitude K hζ S₀ hS η
local notation "H" => sourceThetaPositiveSheet K S bessel p.cutoff hζ v
local notation "C₀" => sourceThetaMellinConstant K S bessel p.cutoff
local notation "A₀" => sourceThetaMellinScale K bessel
local notation "r" => Fintype.card (InfinitePlace K)
local notation "Klog" => sourceThetaGaussianLogKernel C₀ A₀ r

theorem sourceKPPositivePhysicalBranch_quotient
    (e : E) (u : ExteriorUnitSixthClasses S) (g : Finset PE) {t : ℝ} (ht : 0 < t) :
    Integrable (sourceSLocalQuotientSheetFunction S hζ B[e,u,g] hB[e,u,g] t)
        (sNormOneQuotientMeasure K S ν) ∧
      P[e,u,g] t = ∑' i : C × E, A e u g i.1 i.2 * H (t * N (i.1.val + 3 • i.2)) := by
  let _ : Countable E := positiveBranchExponents_countable K S₀
  let _ : Countable C := by unfold ReflectionSquarefreeExponents; infer_instance
  let a (i : C × E) := A e u g i.1 i.2
  let d (i : C × E) := D (sourcePrimeExponentUnit K hζ S₀ (i.1.val + 3 • i.2))
  have hc (w : InfinitePlace K) : 0 < bessel w := mul_pos (by norm_num) Real.pi_pos
  have hd (i : C × E) : sLocalNorm K S (d i) = N (i.1.val + 3 • i.2) :=
    sourcePrimeExponentUnit_fieldSNorm K hζ S₀ (i.1.val + 3 • i.2)
  have ha : Summable (fun i => ‖a i‖ * sLocalNorm K S (d i) ^ (-2 : ℝ)) := by
    simp_rw [hd]
    exact sourceKPPositivePhysicalBranchAmplitude_dirichlet_summable K hζ S₀ hS η e u g (by norm_num)
  have hh (x : Whole) : HasSum (fun i : (C × E) × Γ =>
      a i.1 * sourceThetaPositiveTensor K S bessel p.cutoff ((x * (i.2.val : Whole)) * d i.1))
      (B[e,u,g] x) :=
    sourceKPPositivePhysicalBranchValue_hasSum K hζ S₀ hS η hJ hcut hT p e u g x
  obtain ⟨hi, he⟩ := sourceKPPositiveQuotientSeries_unfold K S hζ v bessel hc p.cutoff
    a d B[e,u,g] hB[e,u,g] hh ha ht
  exact ⟨hi, by simpa only [hd] using he⟩

theorem sourceKPPositivePhysicalBranch_log_integrable
    (e : E) (u : ExteriorUnitSixthClasses S) (g : Finset PE) (x : ℝ) :
    Integrable (fun y : ℝ => Klog y * P[e,u,g] (Real.exp (x + 1 * y))) := by
  let _ : Countable E := positiveBranchExponents_countable K S₀
  let _ : Countable C := by unfold ReflectionSquarefreeExponents; infer_instance
  let a (i : C × E) := A e u g i.1 i.2
  let q (i : C × E) : ℝ := N (i.1.val + 3 • i.2)
  let b (i : C × E) := Real.log (q i)
  let W (t : ℝ) := H (Real.exp t)
  let M (_ : C × E) (t : ℝ) := ‖W t‖
  have hc (w : InfinitePlace K) : 0 < bessel w := mul_pos (by norm_num) Real.pi_pos
  have hq (i : C × E) : 0 < q i := Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos K S₀ _)
  have hW : Measurable W := sourceThetaPositiveSheet_log_measurable K S bessel hc p.cutoff hζ v
  obtain ⟨c, _, hb⟩ := sourceThetaPositiveSheet_log_norm_bound K S bessel hc p.cutoff hζ v 2 (by norm_num)
  have ha : Summable (fun i => ‖a i‖ * Real.exp (-(2 : ℝ) * b i)) := by
    apply (sourceKPPositivePhysicalBranchAmplitude_dirichlet_summable K hζ S₀ hS η e u g
      (σ := 2) (by norm_num)).congr
    intro i
    change ‖a i‖ * q i ^ (-2 : ℝ) = _
    rw [Real.rpow_def_of_pos (hq i), mul_comm (Real.log (q i))]
  obtain ⟨hSum, hInt, _⟩ := sourceThetaGaussianLogAbsSum_bound C₀ A₀ r 1 2 c x a b M
    (fun _ => hW.norm) (fun _ _ => norm_nonneg _) (fun _ t => hb t) ha
  let f (y : ℝ) := Klog y * (∑' i : C × E, a i * W (x + b i + 1 * y))
  have hf : Measurable f :=
    (sourceThetaGaussianLogKernel_continuous C₀ A₀ r).measurable.mul
      (Measurable.tsum fun i => (hW.comp (by fun_prop)).const_mul _)
  have hi : Integrable f := hInt.mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      have hs : Summable (fun i => ‖a i * W (x + b i + 1 * y)‖) := by
        simpa only [norm_mul, M] using hSum y
      have hle := norm_tsum_le_tsum_norm hs
      simp only [norm_mul] at hle
      dsimp only [f]
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hle (norm_nonneg _))
  refine hi.congr (Filter.Eventually.of_forall fun y => ?_)
  apply congrArg (fun z : ℂ => Klog y * z)
  have hP := (sourceKPPositivePhysicalBranch_quotient K hζ S₀ hS η hJ hcut v hT p e u g
    (Real.exp_pos (x + 1 * y))).2
  rw [hP]
  apply tsum_congr
  intro i
  change a i * H (Real.exp (x + b i + 1 * y)) = a i * H (Real.exp (x + 1 * y) * q i)
  rw [show x + b i + 1 * y = (x + 1 * y) + b i by ring, Real.exp_add,
    show Real.exp (b i) = q i from Real.exp_log (hq i)]

end
end ArtinMatthews
