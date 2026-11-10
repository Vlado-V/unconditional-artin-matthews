module

public import ArtinMatthews.SourceKPChartPeriodizationCore
public import ArtinMatthews.SourceKPCompactCoreLocalization
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
public import Mathlib.Tactic.Monotonicity.Lemmas
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
public import Mathlib.Topology.Sheaves.Presheaf
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Positive compact chart tests on the actual arithmetic quotient. -/

namespace ArtinMatthews
open NumberField Filter Topology SourceHyperbolicGreen SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "P" => ProductSpace (InfinitePlace K)
local notation "Ω" => productUpper (InfinitePlace K)
local notation "T" => sourceKPCompactC2Core K hζ

theorem sourceKPCompactChartPullback_mul (f g : Y → ℂ) (b : SourceKPFiniteLevelFiber K hζ) :
    sourceKPCompactChartPullback K hζ (f*g) b =
      sourceKPCompactChartPullback K hζ f b * sourceKPCompactChartPullback K hζ g b := by
  funext x
  by_cases hx : x ∈ Ω <;> simp only [sourceKPCompactChartPullback,hx,ite_true,ite_false,
    Pi.mul_apply,mul_zero]

def sourceKPCompactCoreMul {n : ℕ∞ω} (φ : sourceKPCompactCore K hζ n)
    (f : Y → ℂ) (hf : Continuous f)
    (hd : ∀ b, ContDiffOn ℝ n (sourceKPCompactChartPullback K hζ f b) Ω) :
    sourceKPCompactCore K hζ n :=
  ⟨φ.val*f,φ.prop.1.mul hf,φ.prop.2.1.mul_right,fun b => by
    rw [sourceKPCompactChartPullback_mul]
    exact (φ.prop.2.2 b).mul (hd b)⟩

theorem sourceKPChartPeriodizationGlobal_localized (f : T)
    (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K)
    (η : h1LocalTests (sourceKPFiniteChartCoordinateDomain K hζ b p)) :
    sourceKPChartPeriodizationGlobal K hζ b (sourceKPCompactCoreLocalized K hζ f b p η).val =
      sourceKPChartPeriodizationGlobal K hζ b η.val * f.val := by
  funext y
  by_cases hy : y ∈ Set.range (sourceKPUpperToCompact K hζ b)
  · obtain ⟨x,rfl⟩ := hy
    rw [Pi.mul_apply,sourceKPChartPeriodizationGlobal_apply,sourceKPChartPeriodizationGlobal_apply]
    unfold sourceKPChartPeriodization
    rw [← tsum_mul_right]
    apply tsum_congr
    intro γ
    rw [sourceKPChartPeriodTerm,sourceKPCompactCoreLocalized_apply]
    change η.val.val _ * sourceKPCompactChartPullback K hζ f.val b
      (sourceKPArchUpperEuclideanMap K (γ⁻¹ • x)) = η.val.val _ * f.val _
    have hpos : sourceKPArchUpperEuclideanMap K (γ⁻¹ • x) ∈ Ω :=
      fun v _ => sourceArchUpperEuclideanMap_positive ((γ⁻¹ • x) v)
    rw [sourceKPCompactChartPullback,ite_eq_left hpos,
      sourceKPArchUpperEuclideanMap_left_inverse,sourceKPUpperToCompact_smul]
  · rw [Pi.mul_apply,sourceKPChartPeriodizationGlobal_off K hζ _ _ _ hy,
      sourceKPChartPeriodizationGlobal_off K hζ _ _ _ hy,zero_mul]

theorem sourceKPChartPeriodizationGlobal_real_nonneg (b : SourceKPFiniteLevelFiber K hζ)
    (φ : h1Tests (InfinitePlace K) 2)
    (hφ : ∀ x, 0 ≤ (φ.val x).re ∧ (φ.val x).im = 0) (y : Y) :
    0 ≤ (sourceKPChartPeriodizationGlobal K hζ b φ y).re ∧
      (sourceKPChartPeriodizationGlobal K hζ b φ y).im = 0 := by
  by_cases hy : y ∈ Set.range (sourceKPUpperToCompact K hζ b)
  · obtain ⟨x,rfl⟩ := hy
    obtain ⟨I,hI⟩ := sourceKPChartPeriodTerm_locally_finite K hζ b φ x
    have hz := mem_of_mem_nhds hI
    rw [sourceKPChartPeriodizationGlobal_apply,sourceKPChartPeriodization,
      tsum_eq_sum hz,Complex.re_sum,Complex.im_sum]
    exact ⟨Finset.sum_nonneg (fun γ _ => (hφ _).1),
      Finset.sum_eq_zero (fun γ _ => (hφ _).2)⟩
  · simp only [sourceKPChartPeriodizationGlobal_off K hζ _ _ _ hy,Complex.zero_re,
      Complex.zero_im,le_refl,and_self]

theorem sourceKPChartPeriodizationGlobal_re_ge_one (b : SourceKPFiniteLevelFiber K hζ)
    (φ : h1Tests (InfinitePlace K) 2) (hφ : ∀ x, 0 ≤ (φ.val x).re)
    (p : SourceKPArchUpperHalfSpace K) (hp : φ.val (sourceKPArchUpperEuclideanMap K p) = 1) :
    1 ≤ (sourceKPChartPeriodizationGlobal K hζ b φ (sourceKPUpperToCompact K hζ b p)).re := by
  obtain ⟨I,hI⟩ := sourceKPChartPeriodTerm_locally_finite K hζ b φ p
  have hz := mem_of_mem_nhds hI
  have h1 : sourceKPChartPeriodTerm K hζ b φ 1 p = 1 := by
    simpa only [sourceKPChartPeriodTerm,inv_one,one_smul] using hp
  have hmem : 1 ∈ I := by
    by_contra hn
    exact one_ne_zero (h1.symm.trans (hz 1 hn))
  rw [sourceKPChartPeriodizationGlobal_apply,sourceKPChartPeriodization,
    tsum_eq_sum hz,Complex.re_sum,← Complex.one_re,← h1]
  exact Finset.single_le_sum
    (f := fun γ => (sourceKPChartPeriodTerm K hζ b φ γ p).re)
    (fun γ _ => hφ (sourceKPArchUpperEuclideanMap K (γ⁻¹ • p))) hmem

theorem sourceKPCompactPositiveLocalTest (b : SourceKPFiniteLevelFiber K hζ)
    (p : SourceKPArchUpperHalfSpace K) :
    ∃ η : h1LocalTests (sourceKPFiniteChartCoordinateDomain K hζ b p),
      (∀ x, 0 ≤ (η.val.val x).re ∧ (η.val.val x).im = 0) ∧
      1 ≤ (sourceKPChartPeriodizationGlobal K hζ b η.val (sourceKPUpperToCompact K hζ b p)).re := by
  let U := sourceKPFiniteChartCoordinateDomain K hζ b p
  have hp : sourceKPArchUpperEuclideanMap K p ∈ U :=
    ⟨p,(sourceKPUpperFiniteChart K hζ b p).center_mem,rfl⟩
  obtain ⟨g,hgs,hgc,hgd,hg01,hgp⟩ := exists_contDiff_tsupport_subset (n := (2 : ℕ∞))
    ((sourceKPFiniteChartCoordinateDomain_isOpen K hζ b p).mem_nhds hp)
  let η : h1LocalTests U := ⟨h1RealTest g hgd hgc
      (hgs.trans (sourceKPFiniteChartCoordinateDomain_upper K hζ b p)),
    (tsupport_comp_subset (g := Complex.ofReal) rfl g).trans hgs⟩
  have hη (x : P) : 0 ≤ (η.val.val x).re ∧ (η.val.val x).im = 0 := by
    change 0 ≤ (g x : ℂ).re ∧ (g x : ℂ).im = 0
    simp only [Complex.ofReal_re,Complex.ofReal_im,and_true]
    exact (hg01 ⟨x,rfl⟩).1
  refine ⟨η,hη,sourceKPChartPeriodizationGlobal_re_ge_one K hζ b η.val
    (fun x => (hη x).1) p ?_⟩
  change (g (sourceKPArchUpperEuclideanMap K p) : ℂ) = 1
  rw [hgp,Complex.ofReal_one]

end
end ArtinMatthews
