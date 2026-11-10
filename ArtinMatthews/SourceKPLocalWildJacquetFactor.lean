module

public import ArtinMatthews.SourceKPLocalCompactSeedOrbit
public import ArtinMatthews.SourceKPJacquetStableMap
public import ArtinMatthews.SourceKPJacquetKernel
public import ArtinMatthews.SourceKPJacquetTinyUnits
public import ArtinMatthews.SourceKPLocalBorelRelations
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

/-! All-place stable twisted Jacquet factorization on the actual
finite-dimensional seed orbit at the negative residue parameter. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic SourcePhysical MeasureTheory Filter
open scoped NumberField SourcePhysical Classical
noncomputable section

def SourceKPJacquetFactors {X Y : Type*}
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    (j : X →ₗ[ℂ] Y) (ℓ : X →ₗ[ℂ] ℂ) : Prop :=
  ∃ L₀ : Y →ₗ[ℂ] ℂ, ∀ f : X, L₀ (j f) = ℓ f

theorem sourceKPJacquetFactors_of_ker_le {X Y : Type*}
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    (j : X →ₗ[ℂ] Y) (ℓ : X →ₗ[ℂ] ℂ) (hker : LinearMap.ker j ≤ LinearMap.ker ℓ) :
    SourceKPJacquetFactors j ℓ := by
  letI : AddCommGroup X := Module.addCommMonoidToAddCommGroup ℂ
  letI : AddCommGroup Y := Module.addCommMonoidToAddCommGroup ℂ
  exact sourceKPJacquetLinearFactor_of_ker_le j ℓ hker

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))
    {A : Type*} [Finite A] (v : A → SourceKPAdelicTorusInducedSpace K hζ (-1 / 6 : ℂ))
local notation "L" => P.adicCompletion K
local notation "G" => SourceFiniteKP2Projective K hζ P
local notation "B₀" => SourceFiniteKPProjectiveBorel K hζ P
local notation "W" => sourceKPLocalCompactSeedOrbit K hζ P (-1 / 6 : ℂ) v
local notation "ρ" => sourceKPLocalCompactSeedOrbitRepresentation K hζ P (-1 / 6 : ℂ) v
local notation "B" => sourceLocalBall K P
local notation "ν₀" => sourceLocalValuation K P
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P
local notation "n₀" => fun t : L => l₀ (sourceGL2Upper t)
local notation "w₀" => l₀ sourceGL2Weyl
local notation "ψ₀" => localFiniteCharacter K P
local notation "μ₀" => sourceLocalSelfDual K P

local instance sourceKPLocalWildJacquetValueAddCommGroup : AddCommGroup W := Submodule.addCommGroup _

def sourceKPLocalWildJacquetCoordinates : W ≃ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) := by
  letI : FiniteDimensional ℂ W := sourceKPLocalCompactSeedOrbit_finiteDimensional K hζ P (-1 / 6 : ℂ) v
  exact (Module.finBasis ℂ W).equivFun

local notation "e" => sourceKPLocalWildJacquetCoordinates K hζ P v

theorem sourceKPLocalWildJacquet_upper_fixed (t : L) (u : W) :
    ρ (sourceFiniteKPProjectiveBorelUpper K hζ P t) u = u := by
  apply Subtype.ext
  exact sourceKPAdelicLocalBorelRepresentation_upper K hζ P (-1 / 6 : ℂ) t u.val

theorem sourceKPLocalWildJacquet_unit_cube_fixed (y : Lˣ) (hy : ν₀ ((y ^ 3 : Lˣ) : L) = 1) (u : W) :
    ρ (sourceFiniteKPProjectiveBorelDiagonal K hζ P (y ^ 3)) u = u := by
  apply Subtype.ext
  exact sourceKPJacquet_actual_unit_cube_fixed K P hζ (-1 / 6 : ℂ) y hy u.val

local notation "I₀" => sourceAlgebraicInducedSpace B₀ ρ
local notation "hU" => sourceKPLocalWildJacquet_upper_fixed K hζ P v
local notation "hD" => sourceKPLocalWildJacquet_unit_cube_fixed K hζ P v

def sourceKPLocalWildJacquetMap (C : Submodule ℂ I₀)
    (hSmooth : SourceKPJacquetRootSmooth K hζ P ρ C) : C →ₗ[ℂ] W :=
  sourceKPJacquetStableMap K hζ P ρ C e hU hD hSmooth

theorem sourceKPLocalWildJacquetMap_hasStableValue (C : Submodule ℂ I₀)
    (hSmooth : SourceKPJacquetRootSmooth K hζ P ρ C) (f : C) :
    SourceKPJacquetHasStableValue K hζ P ρ C e f
      (sourceKPLocalWildJacquetMap K hζ P v C hSmooth f) :=
  sourceKPJacquetStableMap_hasStableValue K hζ P ρ C e hU hD hSmooth f

theorem sourceKPLocalWildJacquet_kernel_le (C : Submodule ℂ I₀)
    (hC : ∀ (g : G) (f : I₀), f ∈ C → sourceAlgebraicInducedRepresentation B₀ ρ g f ∈ C)
    (hSmooth : SourceKPJacquetRootSmooth K hζ P ρ C) (ℓ : C →ₗ[ℂ] ℂ)
    (hℓ : ∀ (x : L) (f : C),
      ℓ (sourceKPJacquetRight K hζ P ρ C hC (n₀ x) f) = ψ₀ x * ℓ f) :
    LinearMap.ker (sourceKPLocalWildJacquetMap K hζ P v C hSmooth) ≤ LinearMap.ker ℓ :=
  sourceKPJacquet_kernel_le_whittaker_kernel K hζ P ρ C e hC hU hD hSmooth ℓ hℓ

theorem sourceKPLocalWildJacquet_whittaker_factors (C : Submodule ℂ I₀)
    (hC : ∀ (g : G) (f : I₀), f ∈ C → sourceAlgebraicInducedRepresentation B₀ ρ g f ∈ C)
    (hSmooth : SourceKPJacquetRootSmooth K hζ P ρ C) (ℓ : C →ₗ[ℂ] ℂ)
    (hℓ : ∀ (x : L) (f : C),
      ℓ (sourceKPJacquetRight K hζ P ρ C hC (n₀ x) f) = ψ₀ x * ℓ f) :
    SourceKPJacquetFactors (X := C) (Y := W)
      (sourceKPLocalWildJacquetMap K hζ P v C hSmooth) ℓ :=
  sourceKPJacquetFactors_of_ker_le (X := C) (Y := W)
    (sourceKPLocalWildJacquetMap K hζ P v C hSmooth) ℓ
    (sourceKPLocalWildJacquet_kernel_le K hζ P v C hC hSmooth ℓ hℓ)

end
end ArtinMatthews
