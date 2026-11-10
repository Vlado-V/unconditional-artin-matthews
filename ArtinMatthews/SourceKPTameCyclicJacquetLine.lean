module

public import ArtinMatthews.SourceKPTameCyclicWhittaker
public import ArtinMatthews.SourceKPTameJacquetSignedDiagonal
public import ArtinMatthews.SourceKPTameSphericalTranslateForm
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The vector-valued stable Jacquet map of the actual spherical cyclic
representation has one-dimensional image. The signed diagonal values
and the upper-root equivariance determine the image of every translate. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic AllowedGenerators QuadraticWeil
open scoped NumberField SourcePhysical Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)

local notation "L" => P.val.adicCompletion K
local notation "G₀" => SourceFiniteKP2Projective K hζ P.val
local notation "C₀" => sourceKPTameSphericalCyclicSpace K hζ S₀ P
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P.val
local notation "r₀" => sourceKPTameSphericalCyclicRepresentation K hζ S₀ P
local notation "f₀" => sourceKPTameCyclicSphericalVector K hζ S₀ P
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "J" => sourceKPTameCyclicJacquetMap K hζ S₀ P hS
local notation "λ₀" => sourceKPTameCyclicWhittaker K hζ S₀ P hS

theorem sourceKPTameCyclicJacquetMap_diagonal_line (e : ℤ) :
    ∃ c : ℂ, J (r₀ (l₀ (sourceGL2Diagonal (π₀ ^ e))) f₀) = c • J f₀ := by
  let f := r₀ (l₀ (sourceGL2Diagonal (π₀ ^ e))) f₀
  by_cases he : 0 ≤ e
  · let n := e.toNat
    have hn : (n : ℤ) = e := Int.toNat_of_nonneg he
    have hJ : J f = sourceKPTameJacquetStable K hζ S₀ P n := by
      apply sourceKPTameJacquetHasStableValue_unique K hζ S₀ P
        (sourceKPTameCyclicJacquetMap_hasStableValue K hζ S₀ P hS f)
      dsimp only [f]
      rw [← hn]
      exact sourceKPTameJacquetHasStableValue_diagonal_nonnegative K hζ S₀ P hS n
    change ∃ c : ℂ, J f = c • J f₀
    rw [hJ, sourceKPTameCyclicJacquetMap_spherical]
    let k := n / 3
    have hr : n % 3 < 3 := Nat.mod_lt _ (by decide)
    have hd : n % 3 + 3 * k = n := Nat.mod_add_div n 3
    by_cases hz : n % 3 = 0
    · have h : n = 3 * k := by omega
      rw [h]
      exact ⟨_, sourceKPTameJacquetStable_three K hζ S₀ P hS k⟩
    by_cases ho : n % 3 = 1
    · have h : n = 3 * k + 1 := by omega
      rw [h]
      exact ⟨_, sourceKPTameJacquetStable_three_add_one K hζ S₀ P hS k⟩
    have h : n = 3 * k + 2 := by omega
    rw [h, sourceKPTameJacquetStable_three_add_two K hζ S₀ P hS]
    exact ⟨0, (zero_smul _ _).symm⟩
  · have hP : P.val ∉ traceBadPlaces K := fun h => P.property (hS (Finset.mem_union_left _ h))
    have hz : J f = 0 := sourceKPTameJacquetHasStableValue_unique K hζ S₀ P
      (sourceKPTameCyclicJacquetMap_hasStableValue K hζ S₀ P hS f)
      (sourceKPTameJacquetHasStableValue_diagonal_negative K hζ S₀ P hP e (lt_of_not_ge he))
    exact ⟨0, hz.trans (zero_smul _ _).symm⟩

theorem sourceKPTameCyclicJacquetMap_translate_line (g : G₀) :
    ∃ c : ℂ, J (r₀ g f₀) = c • J f₀ := by
  obtain ⟨c, t, e, hg⟩ := sourceKPTameCyclicSphericalTranslate_normal_form K hζ S₀ P g
  obtain ⟨d, hd⟩ := sourceKPTameCyclicJacquetMap_diagonal_line K hζ S₀ P hS e
  refine ⟨c * (localFiniteCharacter K P.val t * d), ?_⟩
  rw [hg, map_smul, sourceKPTameCyclicJacquetMap_upper, hd, smul_smul, smul_smul, mul_assoc]

theorem sourceKPTameCyclicJacquetMap_mem_line (f : C₀) :
    J f ∈ Submodule.span ℂ {J f₀} := by
  let D := (Submodule.span ℂ {J f₀}).comap J
  have h : C₀ ≤ D.map (Submodule.subtype C₀) := by
    apply Submodule.span_le.mpr
    rintro x ⟨g, rfl⟩
    refine ⟨r₀ g f₀, ?_, rfl⟩
    change J (r₀ g f₀) ∈ Submodule.span ℂ {J f₀}
    obtain ⟨c, hc⟩ := sourceKPTameCyclicJacquetMap_translate_line K hζ S₀ P hS g
    rw [hc]
    exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton _))
  obtain ⟨y, hy, hyf⟩ := h f.property
  have he : y = f := Subtype.ext hyf
  exact he ▸ hy

theorem sourceKPTameCyclicJacquetMap_eq_whittaker_smul (f : C₀) :
    J f = λ₀ f • J f₀ := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (sourceKPTameCyclicJacquetMap_mem_line K hζ S₀ P hS f)
  have h₀ : J f₀ 0 = 1 := sourceKPTameCyclicWhittaker_spherical K hζ S₀ P hS
  have hcoef : λ₀ f = c := by
    change J f 0 = c
    rw [← hc]
    change c * J f₀ 0 = c
    rw [h₀, mul_one]
  rw [hcoef, hc]

end
end ArtinMatthews
