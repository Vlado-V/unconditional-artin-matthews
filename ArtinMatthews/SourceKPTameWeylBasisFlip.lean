module

public import ArtinMatthews.SourceKPTameParametric
public import ArtinMatthews.SourceKPTameParametricAction
public import ArtinMatthews.StandardLocalBallDilation
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

/-! The Weyl change of basis on the actual three-dimensional torus
module, including the unit phase and the local Haar modulus. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic SourcePhysical
open scoped NumberField SourcePhysical
noncomputable section

def sourceKPTameWeylBasisFlip : (ZMod 3 → ℂ) →ₗ[ℂ] (ZMod 3 → ℂ) where
  toFun v i := v (-i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem sourceKPTameWeylBasisFlip_involutive (v : ZMod 3 → ℂ) :
    sourceKPTameWeylBasisFlip (sourceKPTameWeylBasisFlip v) = v := by
  ext i
  change v (- -i) = v i
  exact congrArg v (_root_.neg_neg i)

theorem sourceKPTameWeylBasisFlip_basis (i : ZMod 3) :
    sourceKPTameWeylBasisFlip (sourceJacquetBasis i) = sourceJacquetBasis (-i) := by
  ext j
  change (Pi.single i (1 : ℂ) : ZMod 3 → ℂ) (-j) =
    (Pi.single (-i) (1 : ℂ) : ZMod 3 → ℂ) j
  have he : (-j = i) ↔ (j = -i) := by
    constructor
    · intro h
      exact (_root_.neg_neg j).symm.trans (congrArg (fun k : ZMod 3 => -k) h)
    · intro h
      exact (congrArg (fun k : ZMod 3 => -k) h).trans (_root_.neg_neg i)
  simp only [Pi.single_apply, he]

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "h₆" => source_exterior_six_not_mem K S₀ P.val P.property
local notation "Q₀" => (Ideal.absNorm P.val.asIdeal : ℝ)
local notation "ν₀" => sourceKPFiniteVal K P.val
local notation "τ₀" => sourceKPTameParametricBorelRepresentation K hζ P.val h₆ π₀ hπ₀

theorem sourceKPTameNorm_uniformizer_unit (j : ℤ) (u : Lˣ) (hu : ν₀ (u : L) = 1) :
    ‖((π₀ ^ j * u : Lˣ) : L)‖ = Real.exp (-(j : ℝ) * Real.log Q₀) := by
  have hv := sourceKPValuationOrder_spec ν₀ (π₀ ^ j * u)
  rw [sourceKPValuationOrder_uniformizer_unit K P.val π₀ hπ₀ j u hu] at hv
  change sourceLocalValuation K P.val ((π₀ ^ j * u : Lˣ) : L) = WithZero.exp (-j) at hv
  rw [sourceLocalNorm_eq_zpow K P.val _ (Units.ne_zero _), hv,
    WithZero.log_exp, ← Real.rpow_intCast,
    Real.rpow_def_of_pos (sourceJacquetPrimeNorm_pos K S₀ P)]
  push_cast
  congr 1
  ring

theorem sourceKPTameWeylBasisFlip_diagonal (s : ℂ) (y : Lˣ) :
    sourceKPTameWeylBasisFlip
      (‖(y : L)‖ • τ₀ s (sourceFiniteKPProjectiveBorelDiagonal K hζ P.val y⁻¹)
        (sourceJacquetBasis 0)) =
      τ₀ (-s) (sourceFiniteKPProjectiveBorelDiagonal K hζ P.val y) (sourceJacquetBasis 0) := by
  let j := sourceKPValuationOrder ν₀ y
  let u := sourceKPUnitPart ν₀ π₀ y
  have hu : ν₀ (u : L) = 1 := sourceKPUnitPart_valuation ν₀ π₀ hπ₀ y
  have hy : y = π₀ ^ j * u := (sourceKPUnitPart_factor ν₀ π₀ y).symm
  have hui : ν₀ ((u⁻¹ : Lˣ) : L) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  have hyi : y⁻¹ = π₀ ^ (-j) * u⁻¹ := by
    rw [hy, mul_inv, zpow_neg]
  have hreal (r : ℝ) (v : ZMod 3 → ℂ) : r • v = (r : ℂ) • v := by
    ext i
    rfl
  rw [hyi, hy,
    sourceKPTameParametricBorel_diagonal_unit_basis_zero K hζ S₀ P s (-j) u⁻¹ hui,
    sourceKPTameParametricBorel_diagonal_unit_basis_zero K hζ S₀ P (-s) j u hu,
    sourceKPTameNorm_uniformizer_unit K hζ S₀ P j u hu,
    hreal,
    map_smul, map_smul, sourceKPTameWeylBasisFlip_basis]
  simp only [Int.cast_neg, neg_neg, map_inv, inv_zpow, zpow_neg]
  rw [smul_smul]
  apply congrArg₂ (fun (c : ℂ) (v : ZMod 3 → ℂ) => c • v)
  · change (Complex.ofReal (Real.exp (-(j : ℝ) * Real.log Q₀)) *
      (Complex.exp (-(s + 1 / 2) * -(j : ℂ) * (Real.log Q₀ : ℂ)) *
        ((sourceKPTameUniformizerCharacter K hζ P.val π₀ u ^ j)⁻¹ : ℂˣ))) = _
    rw [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
    push_cast
    congr 2
    ring
  · exact congrArg sourceJacquetBasis (_root_.neg_neg (j : ZMod 3))

end
end ArtinMatthews
