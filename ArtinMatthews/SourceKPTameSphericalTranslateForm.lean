module

public import ArtinMatthews.SourceKPTameCyclicWhittaker
public import ArtinMatthews.SourceKPProjectiveCanonicalFactors
public import ArtinMatthews.SourceKPTameCentralAction
public import ArtinMatthews.SourceKPTameJacquetAllTranslates
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

/-! Every actual spherical translate has an exact form with a scalar,
one upper-root translate and one pure uniformizer diagonal. Iwasawa
and the actual unit phase supply this form for the full group. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic
open scoped NumberField SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "ν₀" => sourceKPFiniteVal K P.val
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "h₆" => source_exterior_six_not_mem K S₀ P.val P.property
local notation "f₀" => sourceKPTameExteriorSphericalSection K hζ S₀ P
local notation "ρ₀" => sourceKPTameExteriorInducedRepresentation K hζ S₀ P
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P.val
local notation "χ₀" => reflectionPrimeCharacters K hζ S₀ P

theorem sourceKPTameSphericalTranslate_normal_form (g : SourceFiniteKP2Projective K hζ P.val) :
    ∃ (c : ℂ) (t : L) (e : ℤ), ρ₀ g f₀ =
      c • ρ₀ (l₀ (sourceGL2Upper t)) (ρ₀ (l₀ (sourceGL2Diagonal (π₀ ^ e))) f₀) := by
  obtain ⟨z, t, y, k, hg⟩ := sourceFiniteKP2Projective_Iwasawa_canonical K hζ P.val h₆ g
  let e := sourceKPValuationOrder ν₀ y
  let u := sourceKPUnitPart ν₀ π₀ y
  have hu : ν₀ (u : L) = 1 := sourceKPUnitPart_valuation ν₀ π₀ hπ₀ y
  have hy : π₀ ^ e * u = y := sourceKPUnitPart_factor ν₀ π₀ y
  let c := χ₀ (sourceKPLocalUnitResidue K P.val u hu) ^ (2 * e)
  have hd : ρ₀ (l₀ (sourceGL2Diagonal y)) f₀ = c • ρ₀ (l₀ (sourceGL2Diagonal (π₀ ^ e))) f₀ := by
    rw [← hy]
    exact sourceKPTameExteriorSpherical_diagonal_unit_phase K hζ S₀ P e u hu
  refine ⟨(sourceKPCentralComplex K hζ P.val z : ℂ) * c, t, e, ?_⟩
  rw [hg]
  simp only [map_mul ρ₀, Module.End.mul_apply, sourceKPTameSphericalSection_right K hζ P.val h₆ π₀ hπ₀ k,
    sourceKPTameInducedRepresentation_center, hd, map_smul, smul_smul]
  rw [mul_comm c (sourceKPCentralComplex K hζ P.val z : ℂ)]

theorem sourceKPTameCyclicSphericalTranslate_normal_form (g : SourceFiniteKP2Projective K hζ P.val) :
    let ρ := sourceKPTameSphericalCyclicRepresentation K hζ S₀ P
    let v := sourceKPTameCyclicSphericalVector K hζ S₀ P
    ∃ (c : ℂ) (t : L) (e : ℤ), ρ g v =
      c • ρ (l₀ (sourceGL2Upper t)) (ρ (l₀ (sourceGL2Diagonal (π₀ ^ e))) v) := by
  obtain ⟨c, t, e, h⟩ := sourceKPTameSphericalTranslate_normal_form K hζ S₀ P g
  exact ⟨c, t, e, Subtype.ext h⟩

end
end ArtinMatthews
