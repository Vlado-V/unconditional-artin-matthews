module

public import ArtinMatthews.SourceKPJacquetDiagonalScalarProfile
public import ArtinMatthews.SourceKPAdelicOutgoingExceptionalJacquetBorel
public import ArtinMatthews.SourceKPJacquetFlatDiagonalEquiv
public import ArtinMatthews.SourceKPJacquetFrequencyCutoff
public import ArtinMatthews.SourceKPJacquetDiagonalStabilized
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

/-! Exact outgoing exceptional Jacquet diagonal data on the actual
all-remainder Borel value space and deep-fixed local section. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain SourcePhysical
open scoped NumberField SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K)) (hs : 0 < (1 / 6 : ℂ).re)
local notation "L" => P.adicCompletion K
local notation "G" => SourceFiniteKP2Projective K hζ P
local notation "B₀" => SourceFiniteKPProjectiveBorel K hζ P
local notation "a₀" => fun z : Lˣ => sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Diagonal z)
local notation "W" => sourceKPAdelicOutgoingRegularizedRetainedCarrier K hζ
  (Singleton.singleton P : Finset (HeightOneSpectrum (𝓞 K))) (1 / 6 : ℂ) hs
local notation "ρ₀" => sourceKPAdelicOutgoingRegularizedLocalBorelRepresentation K hζ P (1 / 6 : ℂ) hs
local notation "hUpper" => sourceKPAdelicOutgoingRegularizedLocalBorelRepresentation_upper K hζ P (1 / 6 : ℂ) hs
local notation "hCube" => sourceKPAdelicOutgoingExceptionalJacquet_negativeCubeLaw K hζ P hs
local notation "D" => sourceKPJacquetDeepFixedSubspace K hζ P ρ₀

local instance sourceKPOutgoingExceptionalProfileValueAddCommGroup : AddCommGroup W := Submodule.addCommGroup _

section DeepSubspace

variable (C : Submodule ℂ (sourceAlgebraicInducedSpace (SourceFiniteKPProjectiveBorel K hζ P)
      (sourceKPAdelicOutgoingRegularizedLocalBorelRepresentation K hζ P (1 / 6 : ℂ) hs)))
    {ι : Type*} [Fintype ι]
    (e : (sourceKPAdelicOutgoingRegularizedRetainedCarrier K hζ
        (Singleton.singleton P : Finset (HeightOneSpectrum (𝓞 K))) (1 / 6 : ℂ) hs) ≃ₗ[ℂ] (ι → ℂ))
    (hC : ∀ (g : SourceFiniteKP2Projective K hζ P)
      (f : sourceAlgebraicInducedSpace (SourceFiniteKPProjectiveBorel K hζ P)
        (sourceKPAdelicOutgoingRegularizedLocalBorelRepresentation K hζ P (1 / 6 : ℂ) hs)),
      f ∈ C → sourceAlgebraicInducedRepresentation (SourceFiniteKPProjectiveBorel K hζ P)
        (sourceKPAdelicOutgoingRegularizedLocalBorelRepresentation K hζ P (1 / 6 : ℂ) hs) g f ∈ C)
    (hDeep : C ≤ sourceKPJacquetDeepFixedSubspace K hζ P
      (sourceKPAdelicOutgoingRegularizedLocalBorelRepresentation K hζ P (1 / 6 : ℂ) hs))
local notation "r₀" => sourceKPJacquetRight K hζ P ρ₀ C hC
local notation "hU" => sourceKPJacquet_unitCube_of_negativeCubeLaw K hζ P ρ₀ hCube
local notation "hSmooth" => sourceKPJacquet_rootSmooth_of_deepFixed K hζ P ρ₀ C hDeep
local notation "J" => sourceKPJacquetStableMap K hζ P ρ₀ C e hUpper hU hSmooth

theorem sourceKPAdelicOutgoingExceptionalJacquetMap_diagonal_cutoff (f : C) :
    ∃ M N : ℕ, ∀ z : Lˣ,
      let u := sourceKPJacquetFrequencyTruncation K hζ P ρ₀ e z
        (sourceKPJacquetFrequencyRadius K P M N z : ℤ) f.val
      SourceKPJacquetFrequencyHasStableValue K hζ P ρ₀ e z f.val u ∧
        J (r₀ (a₀ z) f) = (↑(‖(z : L)‖ ^ (2 / 3 : ℝ)) : ℂ) •
          sourceKPJacquetFlatDiagonalEquiv K hζ P ρ₀ z⁻¹ u :=
  sourceKPJacquetStableMap_diagonal_stabilized K hζ P ρ₀ C e hC hUpper hCube hSmooth f

def sourceKPAdelicOutgoingExceptionalJacquetDiagonalProfile (f : C) (ℓ : W →ₗ[ℂ] ℂ) : Lˣ → ℂ :=
  sourceKPJacquetDiagonalScalarProfile K hζ P ρ₀ C e hC hUpper hCube hDeep f ℓ

local notation "Profile" => sourceKPAdelicOutgoingExceptionalJacquetDiagonalProfile K hζ P hs C e hC hDeep

theorem sourceKPAdelicOutgoingExceptionalJacquetDiagonalProfile_data (f : C) (ℓ : W →ₗ[ℂ] ℂ) :
    Continuous (Profile f ℓ) ∧ ∃ n : ℤ, ∃ A : ℝ, 0 < A ∧
      (∀ z : Lˣ, z ∉ sourceLocalMulBall K P n → Profile f ℓ z = 0) ∧
      ∀ z : Lˣ, z ∈ sourceLocalMulBall K P 0 → ‖Profile f ℓ z‖ ≤ A * ‖(z : L)‖ ^ (1 / 3 : ℝ) :=
  sourceKPJacquetDiagonalScalarProfile_data K hζ P ρ₀ C e hC hUpper hCube hDeep f ℓ

end DeepSubspace

def sourceKPAdelicOutgoingExceptionalJacquetDeepSeed : D := by
  let f := sourceKPAdelicOutgoingRegularizedLocalSection K hζ P (1 / 6 : ℂ) hs
  exact ⟨f.val, sourceKPLocalCompactFixedSpace_le_jacquetDeepFixed K hζ P ρ₀ f.property⟩

def sourceKPAdelicOutgoingExceptionalSeedJacquetDiagonalProfile {ι : Type*} [Fintype ι]
    (e : W ≃ₗ[ℂ] (ι → ℂ)) (ℓ : W →ₗ[ℂ] ℂ) : Lˣ → ℂ :=
  sourceKPAdelicOutgoingExceptionalJacquetDiagonalProfile K hζ P hs D e
    (sourceKPJacquetDeepFixedSubspace_invariant K hζ P ρ₀) le_rfl
    (sourceKPAdelicOutgoingExceptionalJacquetDeepSeed K hζ P hs) ℓ

local notation "SeedProfile" => sourceKPAdelicOutgoingExceptionalSeedJacquetDiagonalProfile K hζ P hs

theorem sourceKPAdelicOutgoingExceptionalSeedJacquetDiagonalProfile_data {ι : Type*} [Fintype ι]
    (e : W ≃ₗ[ℂ] (ι → ℂ)) (ℓ : W →ₗ[ℂ] ℂ) :
    Continuous (SeedProfile e ℓ) ∧ ∃ n : ℤ, ∃ A : ℝ, 0 < A ∧
      (∀ z : Lˣ, z ∉ sourceLocalMulBall K P n → SeedProfile e ℓ z = 0) ∧
      ∀ z : Lˣ, z ∈ sourceLocalMulBall K P 0 → ‖SeedProfile e ℓ z‖ ≤ A * ‖(z : L)‖ ^ (1 / 3 : ℝ) :=
  sourceKPAdelicOutgoingExceptionalJacquetDiagonalProfile_data K hζ P hs D e
    (sourceKPJacquetDeepFixedSubspace_invariant K hζ P ρ₀) le_rfl
    (sourceKPAdelicOutgoingExceptionalJacquetDeepSeed K hζ P hs) ℓ

end
end ArtinMatthews
