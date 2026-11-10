module

public import ArtinMatthews.SourceReflectionClassSelector
public import ArtinMatthews.SourceReflectionNumeratorSeries
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Separating the actual row and column classes commutes with the
absolutely convergent reflected branch. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {U : Type}

local notation "E" => SourcePrimeExponents F S₀
local notation "Prime" => SourceExteriorPrime F S₀
local notation "Q" => SWholePowerClasses F 6 (sourceHilbertSet F S₀)
local notation "C" => sourceReflectionExponentSixthClass F S₀ hζ
local notation "δ" => sourceReflectionClassIndicator F S₀ hζ
local notation "T" => sourceReflectionExpansionTerm F S₀ hζ

/-- The two class restrictions belong to the separate row and column factors. -/
def sourceReflectionExpansionData_withClassSlices
    (A : SourceReflectionExpansionData F S₀ (U × Q × Q)) :
    SourceReflectionExpansionData F S₀ (U × Q × Q) where
  scalar := A.scalar
  row h f a n j d := δ d j.2.1 * A.row h f a n j d
  column h f a n j c := δ c j.2.2 * A.column h f a n j c
  profile := A.profile
  scalar_bound := A.scalar_bound
  row_bound h f a n j d := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (sourceReflectionClassIndicator_norm_le_one F S₀ hζ _ _)).trans (A.row_bound h f a n j d)
  column_bound h f a n j c := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (sourceReflectionClassIndicator_norm_le_one F S₀ hζ _ _)).trans (A.column_bound h f a n j c)
  profile_smooth := A.profile_smooth
  profile_derivative := A.profile_derivative

variable (A : SourceReflectionExpansionData F S₀
  (U × SWholePowerClasses F 6 (sourceHilbertSet F S₀) ×
    SWholePowerClasses F 6 (sourceHilbertSet F S₀)))

theorem sourceReflectionExpansionTerm_withClassSlices (Z : ℝ) (h d : E)
    (f : Finset Prime) (a n c : E) (j : U × Q × Q) :
    T (sourceReflectionExpansionData_withClassSlices F S₀ hζ A) Z h d f a n c j =
      δ d j.2.1 * δ c j.2.2 * T A Z h d f a n c j := by
  simp only [sourceReflectionExpansionTerm, sourceReflectionColumnCoefficient,
    sourceReflectionExpansionData_withClassSlices, mul_div_assoc]
  ring

variable [Fintype U] [Fintype (SWholePowerClasses F 6 (sourceHilbertSet F S₀))]

theorem sourceReflectionExpansionTerm_sum_classSlices (Z : ℝ) (h d : E)
    (f : Finset Prime) (a n c : E) :
    (∑ j : U × Q × Q,
      T (sourceReflectionExpansionData_withClassSlices F S₀ hζ A) Z h d f a n c j) =
    ∑ j : U, T A Z h d f a n c (j, C d, C c) := by
  simp only [Fintype.sum_prod_type, sourceReflectionExpansionTerm_withClassSlices]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single_of_mem (C d) (Finset.mem_univ _)]
  · rw [Finset.sum_eq_single_of_mem (C c) (Finset.mem_univ _)]
    · simp [sourceReflectionClassIndicator]
    · intro sc _ hsc
      simp [sourceReflectionClassIndicator, Ne.symm hsc]
  · intro sd _ hsd
    simp [sourceReflectionClassIndicator, Ne.symm hsd]

theorem sourceReflectionSelectedBranch_sum_classSlices {Z : ℝ} (hZ : 0 < Z)
    (h d : E) (f : Finset Prime) :
    (∑ j : U × Q × Q, sourceReflectionSelectedBranch F S₀ hζ
      (sourceReflectionExpansionData_withClassSlices F S₀ hζ A) Z h d f j (fun _ => True)) =
    ∑' i : SourceReflectionTermIndex F S₀ f,
      ∑ j : U, T A Z h d f i.1.val i.2.1 i.2.2.val (j, C d, C i.2.2.val) := by
  simp only [sourceReflectionSelectedBranch, ite_true]
  rw [← Summable.tsum_finsetSum]
  · exact tsum_congr (fun i => sourceReflectionExpansionTerm_sum_classSlices F S₀ hζ A
      Z h d f i.1.val i.2.1 i.2.2.val)
  · intro j _
    exact (sourceReflectionExpansionTerm_norm_summable F S₀ hζ
      (sourceReflectionExpansionData_withClassSlices F S₀ hζ A) hZ h d f j).of_norm

theorem sourceReflectionSelectedBranch_sum_supportedClassSlices {Z : ℝ} (hZ : 0 < Z)
    (h d : E) (f : Finset Prime)
    (hzero : ∀ (i : SourceReflectionTermIndex F S₀ f), ¬ sourceReflectionTermSupported F S₀ f d i →
      ∀ j : U, T A Z h d f i.1.val i.2.1 i.2.2.val (j, C d, C i.2.2.val) = 0) :
    (∑ j : U × Q × Q, sourceReflectionSelectedBranch F S₀ hζ
      (sourceReflectionExpansionData_withClassSlices F S₀ hζ A) Z h d f j (fun _ => True)) =
    ∑' i : SourceReflectionSupportedTermIndex F S₀ f d,
      ∑ j : U, T A Z h d f i.val.1.val i.val.2.1 i.val.2.2.val (j, C d, C i.val.2.2.val) := by
  rw [sourceReflectionSelectedBranch_sum_classSlices F S₀ hζ A hZ]
  let g (i : SourceReflectionTermIndex F S₀ f) : ℂ :=
    ∑ j : U, T A Z h d f i.1.val i.2.1 i.2.2.val (j, C d, C i.2.2.val)
  have hs : Function.support g ⊆ {i | sourceReflectionTermSupported F S₀ f d i} := by
    intro i hi
    by_contra hbad
    exact hi (Finset.sum_eq_zero (fun j _ => hzero i hbad j))
  exact (tsum_subtype_eq_of_support_subset hs).symm

end
end ArtinMatthews.SourceEulerAssembly
