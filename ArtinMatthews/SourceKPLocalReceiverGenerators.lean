module

public import ArtinMatthews.SourceKPLocalReceiverBasis
public import ArtinMatthews.SourceIntertwiningSubgroup
public import ArtinMatthews.SourceKPTameCentralAction
public import ArtinMatthews.SourceKPLocalBorelRelations
public import ArtinMatthews.SourceKPLocalTorusCharacter
public import ArtinMatthews.SourceKPTameParametricAction
public import ArtinMatthews.SourceKPTameParametricOpenCell
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual receiver intertwines the center, upper root and
uniformizer. The compact-unit step will use the chosen fixed vector. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀) (s : ℂ)

local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "h₆" => source_exterior_six_not_mem K S₀ P.val P.property
local notation "V" => SourceKPAdelicTorusInducedSpace K hζ s
local notation "B" => SourceFiniteKPProjectiveBorel K hζ P.val
local notation "ρ" => sourceKPTameParametricBorelRepresentation K hζ P.val h₆ π₀ hπ₀ s
local notation "σ" => sourceKPAdelicLocalBorelRepresentation K hζ P.val s

def sourceKPLocalReceiverSubgroup (v : V) : Subgroup B :=
  sourceIntertwiningSubgroup ρ σ (sourceKPLocalReceiver K hζ P.val π₀ s v)

theorem sourceKPLocalReceiverSubgroup_center (v : V)
    (z : rootsOfUnity 3 (P.val.adicCompletion K)) :
    sourceFiniteKPProjectiveBorelCenter K hζ P.val z ∈ sourceKPLocalReceiverSubgroup K hζ S₀ P s v := by
  intro f
  change sourceKPLocalReceiver K hζ P.val π₀ s v
      (ρ (sourceFiniteKPProjectiveBorelCenter K hζ P.val z) f) =
    σ (sourceFiniteKPProjectiveBorelCenter K hζ P.val z) (sourceKPLocalReceiver K hζ P.val π₀ s v f)
  rw [sourceKPTameParametricBorel_center K hζ S₀ P, map_smul,
    sourceKPAdelicLocalBorelRepresentation_center]

theorem sourceKPLocalReceiverSubgroup_uniformizer (v : V) :
    sourceFiniteKPProjectiveBorelDiagonal K hζ P.val π₀ ∈ sourceKPLocalReceiverSubgroup K hζ S₀ P s v := by
  intro f
  exact congrArg (fun L : (ZMod 3 → ℂ) →ₗ[ℂ] V => L f)
    (sourceKPLocalReceiver_uniformizer K hζ P.val π₀ h₆ hπ₀ s v)

theorem sourceKPLocalReceiverSubgroup_uniformizer_power (v : V) (j : ℤ) :
    sourceFiniteKPProjectiveBorelDiagonal K hζ P.val (π₀^j) ∈
      sourceKPLocalReceiverSubgroup K hζ S₀ P s v := by
  have h := (sourceKPLocalReceiverSubgroup K hζ S₀ P s v).zpow_mem
    (sourceKPLocalReceiverSubgroup_uniformizer K hζ S₀ P s v) j
  rw [← sourceKPLocalUniformizer_diagonal_zpow K hζ P.val π₀ j] at h
  exact h

theorem sourceKPLocalReceiverSubgroup_upper (v : V) (x : P.val.adicCompletion K) :
    sourceFiniteKPProjectiveBorelUpper K hζ P.val x ∈ sourceKPLocalReceiverSubgroup K hζ S₀ P s v := by
  intro f
  change sourceKPLocalReceiver K hζ P.val π₀ s v
      (ρ (sourceFiniteKPProjectiveBorelUpper K hζ P.val x) f) =
    σ (sourceFiniteKPProjectiveBorelUpper K hζ P.val x) (sourceKPLocalReceiver K hζ P.val π₀ s v f)
  rw [sourceKPTameParametricBorel_upper K hζ S₀ P, sourceKPAdelicLocalBorelRepresentation_upper]

theorem sourceKPLocalParametricBorel_unit_zero (u : (P.val.adicCompletion K)ˣ)
    (hu : sourceKPFiniteVal K P.val (u : P.val.adicCompletion K) = 1) :
    ρ (sourceFiniteKPProjectiveBorelDiagonal K hζ P.val u) (sourceJacquetBasis 0) = sourceJacquetBasis 0 := by
  have h := sourceKPTameParametricBorel_diagonal_unit_basis_zero K hζ S₀ P s (0 : ℤ) u hu
  simpa only [zpow_zero, one_mul, Int.cast_zero, neg_zero, mul_zero, zero_mul,
    Complex.exp_zero, Units.val_one, one_smul] using h

end
end ArtinMatthews
