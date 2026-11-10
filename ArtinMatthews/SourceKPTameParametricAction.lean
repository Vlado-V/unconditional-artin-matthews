module

public import ArtinMatthews.SourceKPTameCentralAction
public import ArtinMatthews.SourceKPTameParametric
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

/-! The actual right action on the parameter-dependent induced
space, compact invariance of its distinguished vector, and the
full unit phase in its diagonal value. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic QuadraticWeil AllowedGenerators Matrix
open scoped NumberField MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "G₀" => SourceFiniteKP2Projective K hζ P.val
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "h₆" => source_exterior_six_not_mem K S₀ P.val P.property
local notation "Q₀" => (Ideal.absNorm P.val.asIdeal : ℝ)
local notation "ν₀" => sourceKPFiniteVal K P.val
local notation "κ₀" => sourceFiniteKP2ProjectiveCompactSection K hζ P.val h₆
local notation "τ₀" => sourceKPTameParametricBorelRepresentation K hζ P.val h₆ π₀ hπ₀

def sourceKPTameParametricInducedRepresentation (s : ℂ) :
    Representation ℂ G₀ (SourceKPTameParametricInducedSpace K hζ P.val h₆ π₀ hπ₀ s) :=
  sourceAlgebraicInducedRepresentation (sourceFiniteKPNormalizedBorelToProjective K hζ P.val).range (τ₀ s)

theorem sourceKPTameParametricSpherical_right (s : ℂ) (k : SourceFiniteKP2Integral K P.val) :
    sourceKPTameParametricInducedRepresentation K hζ S₀ P s (κ₀ k)
      (sourceKPTameParametricSphericalSection K hζ P.val h₆ π₀ hπ₀ s) =
        sourceKPTameParametricSphericalSection K hζ P.val h₆ π₀ hπ₀ s := by
  let c : SourceFiniteKP2ProjectiveCompact K hζ P.val h₆ := ⟨κ₀ k, ⟨k, rfl⟩⟩
  exact sourceAlgebraicSphericalSection_right _ _ _ _ _ _ c

theorem sourceKPTameParametricSpherical_eval_right (s : ℂ) (k : SourceFiniteKP2Integral K P.val) (g : G₀) :
    (sourceKPTameParametricSphericalSection K hζ P.val h₆ π₀ hπ₀ s).val (g * κ₀ k) =
      (sourceKPTameParametricSphericalSection K hζ P.val h₆ π₀ hπ₀ s).val g :=
  congrArg (fun f : SourceKPTameParametricInducedSpace K hζ P.val h₆ π₀ hπ₀ s => f.val g)
    (sourceKPTameParametricSpherical_right K hζ S₀ P s k)

theorem sourceKPTameBorelTwist_center (s : ℂ) (z : rootsOfUnity 3 L) :
    sourceKPTameBorelTwist K hζ P.val s (sourceFiniteKPProjectiveBorelCenter K hζ P.val z) = 1 := by
  rw [sourceFiniteKPProjectiveBorelCenter, sourceKPTameBorelTwist_normalized]
  change Complex.exp (-(s + 1 / 6) * (sourceKPValuationOrder ν₀ (GeneralLinearGroup.det (1 : GL (Fin 2) L)) : ℂ) *
    (Real.log Q₀ : ℂ)) = 1
  rw [map_one, sourceKPValuationOrder_one]
  simp

theorem sourceKPTameParametricBorel_center (s : ℂ) (z : rootsOfUnity 3 L) (v : ZMod 3 → ℂ) :
    τ₀ s (sourceFiniteKPProjectiveBorelCenter K hζ P.val z) v =
      (sourceKPCentralComplex K hζ P.val z : ℂ) • v := by
  change sourceKPTameBorelTwist K hζ P.val s _ •
    sourceKPTameBorelRepresentation K hζ P.val h₆ π₀ hπ₀ _ v = _
  rw [sourceKPTameBorelTwist_center, one_smul, sourceKPTameBorelRepresentation_center]

theorem sourceKPTameParametricSpherical_center (s : ℂ) (z : rootsOfUnity 3 L) (g : G₀) :
    (sourceKPTameParametricSphericalSection K hζ P.val h₆ π₀ hπ₀ s).val
      (sourceFiniteKP2ProjectiveCenter K hζ P.val z * g) =
        (sourceKPCentralComplex K hζ P.val z : ℂ) •
          (sourceKPTameParametricSphericalSection K hζ P.val h₆ π₀ hπ₀ s).val g := by
  rw [← sourceFiniteKPProjectiveBorelCenter_val,
    sourceKPTameParametricSpherical_covariant, sourceKPTameParametricBorel_center]

theorem sourceKPTameParametricBorel_diagonal_unit_basis_zero (s : ℂ) (j : ℤ) (u : Lˣ)
    (hu : ν₀ (u : L) = 1) :
    τ₀ s (sourceFiniteKPProjectiveBorelDiagonal K hζ P.val (π₀ ^ j * u)) (sourceJacquetBasis 0) =
      (Complex.exp (-(s + 1 / 2) * (j : ℂ) * (Real.log Q₀ : ℂ)) *
        ((sourceKPTameUniformizerCharacter K hζ P.val π₀ u ^ (-j) : ℂˣ) : ℂ)) •
          sourceJacquetBasis (j : ZMod 3) := by
  change sourceKPTameBorelTwist K hζ P.val s _ •
    sourceKPTameBorelRepresentation K hζ P.val h₆ π₀ hπ₀ _ (sourceJacquetBasis 0) = _
  rw [sourceKPTameBorelTwist_diagonal,
    sourceKPValuationOrder_uniformizer_unit K P.val π₀ hπ₀ j u hu,
    sourceKPTameBorelRepresentation_uniformizer_unit_basis_zero K hζ P.val h₆ π₀ hπ₀ j u hu,
    smul_smul]
  congr 1
  rw [sourceJacquetScale, Real.rpow_def_of_pos (sourceJacquetPrimeNorm_pos K S₀ P),
    Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  push_cast
  congr 2
  ring

end
end ArtinMatthews
