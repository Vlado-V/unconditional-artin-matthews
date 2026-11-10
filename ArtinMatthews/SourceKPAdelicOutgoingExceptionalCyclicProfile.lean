module

public import ArtinMatthews.SourceKPAdelicOutgoingLocalStableJacquet
public import ArtinMatthews.SourceKPJacquetFlatDiagonalEquiv
public import ArtinMatthews.SourceKPJacquetFrequencyCutoff
public import ArtinMatthews.SourceLocalMultiplicativeShell
public import ArtinMatthews.SourceKPAdelicOutgoingExceptionalJacquetDiagonal
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

/-! The exceptional outgoing cyclic Jacquet map has the exact diagonal
transport and scalar profile data on its literal all-remainder carrier. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain SourcePhysical
open scoped NumberField SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K)) (hs : 0 < (1 / 6 : ℂ).re)
local notation "L" => P.adicCompletion K
local notation "W" => sourceKPAdelicOutgoingRegularizedRetainedCarrier K hζ
  (Singleton.singleton P : Finset (HeightOneSpectrum (𝓞 K))) (1 / 6 : ℂ) hs
local notation "ρ₀" => sourceKPAdelicOutgoingRegularizedLocalBorelRepresentation K hζ P (1 / 6 : ℂ) hs
local notation "C" => sourceKPAdelicOutgoingRegularizedLocalCyclic K hζ P (1 / 6 : ℂ) hs
local notation "e" => sourceKPAdelicOutgoingRegularizedLocalJacquetCoordinates K hζ P (1 / 6 : ℂ) hs
local notation "J" => sourceKPAdelicOutgoingRegularizedLocalJacquetMap K hζ P (1 / 6 : ℂ) hs
local notation "hC" => sourceKPAdelicOutgoingRegularizedLocalCyclic_invariant K hζ P (1 / 6 : ℂ) hs
local notation "hDeep" => sourceKPAdelicOutgoingRegularizedLocalCyclic_le_deepFixed K hζ P (1 / 6 : ℂ) hs
local notation "r₀" => sourceKPJacquetRight K hζ P ρ₀ C hC
local notation "a₀" => fun z : Lˣ => sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Diagonal z)

local instance sourceKPOutgoingExceptionalCyclicProfileAddCommGroup : AddCommGroup W := Submodule.addCommGroup _

theorem sourceKPAdelicOutgoingExceptionalCyclicJacquet_diagonal_cutoff (f : C) :
    ∃ M N : ℕ, ∀ z : Lˣ,
      let u := sourceKPJacquetFrequencyTruncation K hζ P ρ₀ e z
        (sourceKPJacquetFrequencyRadius K P M N z : ℤ) f.val
      SourceKPJacquetFrequencyHasStableValue K hζ P ρ₀ e z f.val u ∧
        J (r₀ (a₀ z) f) = (↑(‖(z : L)‖ ^ (2 / 3 : ℝ)) : ℂ) •
          sourceKPJacquetFlatDiagonalEquiv K hζ P ρ₀ z⁻¹ u :=
  sourceKPAdelicOutgoingExceptionalJacquetMap_diagonal_cutoff K hζ P hs C e hC hDeep f

theorem sourceKPAdelicOutgoingExceptionalCyclicJacquet_diagonal_data (f : C) (ℓ : W →ₗ[ℂ] ℂ) :
    let F : Lˣ → ℂ := fun z => ℓ (J (r₀ (a₀ z) f))
    Continuous F ∧ ∃ n : ℤ, ∃ A : ℝ, 0 < A ∧
      (∀ z : Lˣ, z ∉ sourceLocalMulBall K P n → F z = 0) ∧
      ∀ z : Lˣ, z ∈ sourceLocalMulBall K P 0 → ‖F z‖ ≤ A * ‖(z : L)‖ ^ (1 / 3 : ℝ) :=
  sourceKPAdelicOutgoingExceptionalJacquetDiagonalProfile_data K hζ P hs C e hC hDeep f ℓ

end
end ArtinMatthews
