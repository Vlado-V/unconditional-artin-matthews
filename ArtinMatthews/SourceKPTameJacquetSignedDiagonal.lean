module

public import ArtinMatthews.SourceKPTameJacquetStable
public import ArtinMatthews.SourceKPTameJacquetStableDomain
public import ArtinMatthews.SourceJacquetAdditiveTranslation
public import ArtinMatthews.SourceKPProjectiveSections
public import ArtinMatthews.SourceKPTameJacquetSignedIntegrability
public import ArtinMatthews.SourceKPTameJacquetWhittaker
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
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TotallySplit
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

/-! Stable integration for every pure torus translate of the actual
spherical vector. A negative valuation gives a nontrivial additive
character on the conjugated integral upper subgroup, forcing zero. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic SourcePhysical AllowedGenerators QuadraticWeil Filter
open scoped NumberField SourcePhysical MatrixGroups Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "ν₀" => sourceLocalValuation K P.val
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "h₆" => source_exterior_six_not_mem K S₀ P.val P.property
local notation "f₀" => sourceKPTameExteriorSphericalSection K hζ S₀ P
local notation "ρ₀" => sourceKPTameExteriorInducedRepresentation K hζ S₀ P
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P.val
local notation "ψ₀" => localFiniteCharacter K P.val
local notation "B" => sourceLocalBall K P.val

theorem sourceKPTameExteriorSpherical_upper_integral_right (u : L) (hu : ν₀ u ≤ 1) :
    ρ₀ (l₀ (sourceGL2Upper u)) f₀ = f₀ := by
  let k : SourceFiniteKP2Integral K P.val := ⟨sourceGL2Upper u, sourceKPIntegralMatrix_upper ν₀ u hu⟩
  have hk : sourceFiniteKP2ProjectiveCompactSection K hζ P.val h₆ k = l₀ (sourceGL2Upper u) :=
    congrArg (sourceFiniteKP2ProjectiveMk K hζ P.val) (sourceFiniteKP2CompactSection_upper K hζ P.val h₆ u hu)
  rw [← hk]
  exact sourceKPTameSphericalSection_right K hζ P.val h₆ π₀ hπ₀ k

theorem sourceKPTameJacquetHasStableValue_diagonal_nonnegative
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) (e : ℕ) :
    sourceKPTameJacquetHasStableValue K hζ S₀ P (ρ₀ (l₀ (sourceGL2Diagonal (π₀ ^ (e : ℤ)))) f₀)
      (sourceKPTameJacquetStable K hζ S₀ P e) := by
  have hP : P.val ∉ traceBadPlaces K := fun h => P.property (hS (Finset.mem_union_left _ h))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  exact ⟨(sourceKPTameJacquetTruncation_formula K hζ S₀ P hP e N).1,
    (sourceKPTameJacquetTruncation_stable K hζ S₀ P hS e N hN).trans
      (sourceKPTameJacquetStable_eq_shellVector K hζ S₀ P hS e).symm⟩

theorem sourceKPTameJacquetHasStableValue_diagonal_negative (hP : P.val ∉ traceBadPlaces K) (e : ℤ) (he : e < 0) :
    sourceKPTameJacquetHasStableValue K hζ S₀ P (ρ₀ (l₀ (sourceGL2Diagonal (π₀ ^ e))) f₀) 0 := by
  let y := π₀ ^ e
  let f := ρ₀ (l₀ (sourceGL2Diagonal y)) f₀
  have hy : (y : L) ∉ B 0 := by
    intro h
    change ν₀ (y : L) ≤ WithZero.exp (0 : ℤ) at h
    dsimp only [y] at h
    rw [Units.val_zpow_eq_zpow_val, sourceJacquetFrequency_valuation K P.val _ hπ₀, WithZero.exp_le_exp] at h
    omega
  obtain ⟨u, hu, hψ⟩ : ∃ u ∈ P.val.adicCompletionIntegers K, ψ₀ ((y : L) * u) ≠ 1 := by
    by_contra! h
    have hc := (sourceLocalInteger_annihilator_iff K P.val (y : L)).mp h
    rw [(sourceDifferentExponent_eq_zero_iff K P.val).mpr hP, Nat.cast_zero] at hc
    exact hy hc
  let t := (y : L) * u
  have htψ : ψ₀ t ≠ 1 := hψ
  have hν : ν₀ u ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K P.val).mp hu
  have huFix := sourceKPTameExteriorSpherical_upper_integral_right K hζ S₀ P u hν
  have hd := sourceFiniteKP2ProjectiveLift_upper_diagonal K hζ P.val t y
  have hdiv : t / (y : L) = u := mul_div_cancel_left₀ u y.ne_zero
  rw [hdiv] at hd
  have hfix : ρ₀ (l₀ (sourceGL2Upper t)) f = f := by
    change ρ₀ (l₀ (sourceGL2Upper t)) (ρ₀ (l₀ (sourceGL2Diagonal y)) f₀) = _
    rw [← Module.End.mul_apply, ← map_mul, hd, map_mul, Module.End.mul_apply, huFix]
  filter_upwards [sourceKPTameJacquetIntegrableOn_eventually_signed K hζ S₀ P hP e,
    sourceJacquetBall_eventually_contains K P.val t] with N hI ht
  refine ⟨hI, ?_⟩
  let j := sourceKPTameJacquetInducedTruncation K hζ S₀ P f N
  have h := sourceKPTameJacquetInducedTruncation_upper K hζ S₀ P f t N ht
  rw [hfix] at h
  change j = ψ₀ t • j at h
  have hz : (ψ₀ t - 1) • j = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr htψ)

theorem sourceKPTameJacquetHasStableValue_diagonal_uniformizer
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) (e : ℤ) :
    ∃ j, sourceKPTameJacquetHasStableValue K hζ S₀ P (ρ₀ (l₀ (sourceGL2Diagonal (π₀ ^ e))) f₀) j := by
  by_cases he : 0 ≤ e
  · have hn : (e.toNat : ℤ) = e := Int.toNat_of_nonneg he
    exact ⟨sourceKPTameJacquetStable K hζ S₀ P e.toNat,
      hn ▸ sourceKPTameJacquetHasStableValue_diagonal_nonnegative K hζ S₀ P hS e.toNat⟩
  · have hP : P.val ∉ traceBadPlaces K := fun h => P.property (hS (Finset.mem_union_left _ h))
    exact ⟨0, sourceKPTameJacquetHasStableValue_diagonal_negative K hζ S₀ P hP e (lt_of_not_ge he)⟩

end
end ArtinMatthews
