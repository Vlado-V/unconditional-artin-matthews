module

public import ArtinMatthews.SourceKPTameCyclicWhittaker
public import ArtinMatthews.SourceKPTameJacquetAllTranslates
public import ArtinMatthews.SourceKPTameJacquetSignedDiagonal
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

/-! Exact local Whittaker values on the constructed cyclic
representation. All signed torus valuations and the actual unit
phase are recovered from the stabilized measured functional. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic AllowedGenerators QuadraticWeil VaryingKummerAnalytic
open scoped NumberField SourcePhysical MatrixGroups Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)

local notation "L" => P.val.adicCompletion K
local notation "G₀" => SourceFiniteKP2Projective K hζ P.val
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P.val
local notation "r₀" => sourceKPTameSphericalCyclicRepresentation K hζ S₀ P
local notation "f₀" => sourceKPTameCyclicSphericalVector K hζ S₀ P
local notation "χ₀" => reflectionPrimeCharacters K hζ S₀ P
local notation "Q₀" => (Ideal.absNorm P.val.asIdeal : ℝ)

def sourceKPTameCyclicWhittakerValue (g : G₀) : ℂ :=
  sourceKPTameCyclicWhittaker K hζ S₀ P hS (r₀ g f₀)

local notation "W₀" => sourceKPTameCyclicWhittakerValue K hζ S₀ P hS

theorem sourceKPTameCyclicWhittakerValue_one : W₀ 1 = 1 := by
  unfold sourceKPTameCyclicWhittakerValue
  rw [map_one r₀]
  exact sourceKPTameCyclicWhittaker_spherical K hζ S₀ P hS

theorem sourceKPTameCyclicWhittakerValue_upper (t : L) (g : G₀) :
    W₀ (l₀ (sourceGL2Upper t) * g) = localFiniteCharacter K P.val t * W₀ g := by
  unfold sourceKPTameCyclicWhittakerValue
  rw [map_mul r₀, Module.End.mul_apply, sourceKPTameCyclicWhittaker_upper]

theorem sourceKPTameCyclicWhittakerValue_diagonal_nonnegative (e : ℕ) :
    W₀ (l₀ (sourceGL2Diagonal (π₀ ^ (e : ℤ)))) = sourceKPTameJacquetStable K hζ S₀ P e 0 := by
  let f := r₀ (l₀ (sourceGL2Diagonal (π₀ ^ (e : ℤ)))) f₀
  have h := sourceKPTameJacquetHasStableValue_unique K hζ S₀ P
    (sourceKPTameCyclicJacquetMap_hasStableValue K hζ S₀ P hS f)
    (sourceKPTameJacquetHasStableValue_diagonal_nonnegative K hζ S₀ P hS e)
  exact congrFun h 0

theorem sourceKPTameCyclicWhittakerValue_diagonal_negative (e : ℤ) (he : e < 0) :
    W₀ (l₀ (sourceGL2Diagonal (π₀ ^ e))) = 0 := by
  let f := r₀ (l₀ (sourceGL2Diagonal (π₀ ^ e))) f₀
  have hP : P.val ∉ traceBadPlaces K := fun h => P.property (hS (Finset.mem_union_left _ h))
  have h := sourceKPTameJacquetHasStableValue_unique K hζ S₀ P
    (sourceKPTameCyclicJacquetMap_hasStableValue K hζ S₀ P hS f)
    (sourceKPTameJacquetHasStableValue_diagonal_negative K hζ S₀ P hP e he)
  exact congrFun h 0

theorem sourceKPTameCyclicWhittakerValue_diagonal_unit (e : ℤ) (u : Lˣ)
    (hu : sourceKPFiniteVal K P.val (u : L) = 1) :
    W₀ (l₀ (sourceGL2Diagonal (π₀ ^ e * u))) =
      χ₀ (sourceKPLocalUnitResidue K P.val u hu) ^ (2 * e) * W₀ (l₀ (sourceGL2Diagonal (π₀ ^ e))) := by
  have hf : r₀ (l₀ (sourceGL2Diagonal (π₀ ^ e * u))) f₀ =
      χ₀ (sourceKPLocalUnitResidue K P.val u hu) ^ (2 * e) • r₀ (l₀ (sourceGL2Diagonal (π₀ ^ e))) f₀ := by
    apply Subtype.ext
    exact sourceKPTameExteriorSpherical_diagonal_unit_phase K hζ S₀ P e u hu
  unfold sourceKPTameCyclicWhittakerValue
  rw [hf, map_smul]
  rfl

theorem sourceKPTameCyclicWhittakerValue_diagonal_three (k : ℕ) :
    W₀ (l₀ (sourceGL2Diagonal (π₀ ^ ((3 * k : ℕ) : ℤ)))) = sourceJacquetScale Q₀ (-(k : ℝ)) := by
  rw [sourceKPTameCyclicWhittakerValue_diagonal_nonnegative,
    sourceKPTameJacquetStable_three K hζ S₀ P hS k]
  change sourceJacquetScale Q₀ (-(k : ℝ)) * sourceKPTameJacquetStable K hζ S₀ P 0 0 = _
  rw [sourceKPTameJacquetStable_zero_at_zero K hζ S₀ P hS, mul_one]

theorem sourceKPTameCyclicWhittakerValue_diagonal_three_add_one (k : ℕ) :
    W₀ (l₀ (sourceGL2Diagonal (π₀ ^ ((3 * k + 1 : ℕ) : ℤ)))) =
      sourceJacquetScale Q₀ (-(k : ℝ) - 1 / 2) * sourceJacquetActualGauss K hζ S₀ P 2 := by
  rw [sourceKPTameCyclicWhittakerValue_diagonal_nonnegative,
    sourceKPTameJacquetStable_three_add_one K hζ S₀ P hS k]
  change (sourceJacquetScale Q₀ (-(k : ℝ) - 1 / 2) * sourceJacquetActualGauss K hζ S₀ P 2) *
    sourceKPTameJacquetStable K hζ S₀ P 0 0 = _
  rw [sourceKPTameJacquetStable_zero_at_zero K hζ S₀ P hS, mul_one]

theorem sourceKPTameCyclicWhittakerValue_diagonal_three_add_two (k : ℕ) :
    W₀ (l₀ (sourceGL2Diagonal (π₀ ^ ((3 * k + 2 : ℕ) : ℤ)))) = 0 := by
  rw [sourceKPTameCyclicWhittakerValue_diagonal_nonnegative,
    sourceKPTameJacquetStable_three_add_two K hζ S₀ P hS k]
  rfl

end
end ArtinMatthews
