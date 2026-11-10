module

public import ArtinMatthews.SourceKPTameJacquetPoint
public import ArtinMatthews.SourceKPExteriorTorusValues
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

/-! The exact Bruhat shell value of the genuine spherical section.
The unit weight is the literal residue-masked character of the checked
Haar shells. The inverse-square orientation and the modular factor
enter before integration. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic
open scoped NumberField
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "ν₀" => sourceKPFiniteVal K P.val
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "h₆" => source_exterior_six_not_mem K S₀ P.val P.property
local notation "Q₀" => (Ideal.absNorm P.val.asIdeal : ℝ)
local notation "χ₀" => reflectionPrimeCharacters K hζ S₀ P
local notation "r₀" => sourceKPTameUniformizerCharacter K hζ P.val π₀

theorem sourceBruhatDiagonal_uniformizer {F : Type*} [Field F] (π u : Fˣ) (l : ℤ) :
    sourceBruhatDiagonal (π ^ (-l) * u) = π ^ (2 * l) * (sourceMinusOneUnit F * u ^ (-2 : ℤ)) := by
  have h (y : Fˣ) : sourceBruhatDiagonal y = sourceMinusOneUnit F * y ^ (-2 : ℤ) := by
    apply Units.ext
    change -((y : F)⁻¹) ^ 2 = ((sourceMinusOneUnit F * y ^ (-2 : ℤ) : Fˣ) : F)
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val]
    simp [sourceMinusOneUnit, zpow_neg, inv_pow]
  rw [h, mul_zpow, ← zpow_mul, show (-l) * (-2) = 2 * l by ring, mul_left_comm]

theorem sourceKPTameExteriorShellUnitPhase (l : ℕ) (u : Lˣ) (hu : ν₀ (u : L) = 1) :
    ((r₀ (sourceMinusOneUnit L * u ^ (-2 : ℤ)) ^ (-(2 * (l : ℤ))) : ℂˣ) : ℂ) =
      sourceJacquetWeight K P.val (sourceJacquetShellCharacter K P.val χ₀ l) (u : L) := by
  have hm : r₀ (sourceMinusOneUnit L) = 1 := by
    rw [sourceKPTameUniformizerCharacter_apply, sourceFiniteKPHilbert_minus_right, one_pow, map_one]
  rw [map_mul r₀, hm, one_mul, map_zpow r₀, ← zpow_mul, Units.val_zpow_eq_zpow_val,
    sourceKPTameExteriorCharacter_residue K hζ S₀ P u hu, ← zpow_mul]
  rw [show (-2 : ℤ) * ((-2) * (-(2 * (l : ℤ)))) = -(8 * (l : ℤ)) by ring]
  rw [sourceJacquetShellCharacter_eq_negative K P.val χ₀ (sourceJacquetActualCharacter_order K hζ S₀ P) l]
  have hw := sourceJacquetWeight_on_integers K P.val (χ₀ ^ (-(8 * (l : ℤ))))
    (sourceKPLocalUnitInteger K P.val u hu)
  change sourceJacquetWeight K P.val _ (u : L) = _ at hw
  rw [hw]
  let : P.val.asIdeal.IsMaximal := P.val.isMaximal
  let : Field ((𝓞 K) ⧸ P.val.asIdeal) := Ideal.Quotient.field _
  let a := Units.mk0 (sourceKPLocalUnitResidue K P.val u hu) (sourceKPLocalUnitResidue_ne_zero K P.val u hu)
  let n := -(8 * (l : ℤ))
  change χ₀ (a : (𝓞 K) ⧸ P.val.asIdeal) ^ n = (χ₀ ^ n) (a : (𝓞 K) ⧸ P.val.asIdeal)
  rw [MulChar.zpow_apply_coe, ← MulChar.coe_toUnitHom χ₀ (a ^ n), map_zpow (MulChar.toUnitHom χ₀),
    Units.val_zpow_eq_zpow_val, MulChar.coe_toUnitHom]

theorem sourceKPTameJacquetPoint_scaled_shell (e : ℤ) (l : ℕ) (u : Lˣ) (hu : ν₀ (u : L) = 1) :
    sourceKPTameJacquetPoint K hζ S₀ P e ((π₀ : L) ^ e * ((π₀ : L) ^ (-(l : ℤ)) * (u : L))) =
      (sourceJacquetScale Q₀ (((e : ℝ) - 2 * (l : ℝ)) / 3) *
        sourceJacquetWeight K P.val (sourceJacquetShellCharacter K P.val χ₀ l) (u : L)) •
        sourceJacquetBasis ((2 * (l : ℤ) - e : ℤ) : ZMod 3) := by
  let H := π₀ ^ (-(l : ℤ)) * u
  let v := sourceMinusOneUnit L * u ^ (-2 : ℤ)
  have hH : (H : L) = (π₀ : L) ^ (-(l : ℤ)) * (u : L) := by
    dsimp only [H]
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val]
  have hval : ν₀ (H : L) = WithZero.exp (l : ℤ) := by
    rw [sourceKPValuationOrder_spec ν₀ H, sourceKPValuationOrder_uniformizer_unit K P.val π₀ hπ₀ (-(l : ℤ)) u hu,
      neg_neg]
  have hHinv : ν₀ ((H : L)⁻¹) ≤ 1 := by
    rw [map_inv₀, hval]
    exact inv_le_one_of_one_le₀ (WithZero.one_le_exp_iff.mpr (Int.natCast_nonneg l))
  have hdiag : sourceBruhatDiagonal H = π₀ ^ (2 * (l : ℤ)) * v :=
    sourceBruhatDiagonal_uniformizer π₀ u l
  have hminus : ν₀ (sourceMinusOneUnit L : L) = 1 := by
    change ν₀ (-1 : L) = 1
    rw [Valuation.map_neg, map_one]
  have hv : ν₀ (v : L) = 1 := by
    dsimp only [v]
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hminus, hu, one_zpow, mul_one]
  have hQ := sourceJacquetPrimeNorm_pos K S₀ P
  rw [sourceKPTameJacquetPoint_mul_uniformizer, ← hH,
    sourceKPTameExteriorSpherical_weyl_upper_bruhat K hζ S₀ P H hHinv, hdiag,
    sourceKPTameBorelRepresentation_uniformizer_unit_basis_zero _ _ _ _ _ _ (2 * (l : ℤ)) v hv,
    map_smul, sourceKPTameBorelRepresentation_uniformizer_basis,
    smul_smul, mul_comm (_ * _), ← mul_assoc, ← sourceJacquetScale_add hQ]
  have hp := sourceKPTameExteriorShellUnitPhase K hζ S₀ P l u hu
  change ((r₀ v ^ (-(2 * (l : ℤ))) : ℂˣ) : ℂ) = _ at hp
  rw [hp, ← Int.cast_add, show 2 * (l : ℤ) + -e = 2 * (l : ℤ) - e by ring]
  rw [show (-(↑(-e : ℤ) : ℝ) / 3 + -(↑(2 * (l : ℤ)) : ℝ) / 3) =
    ((e : ℝ) - 2 * (l : ℝ)) / 3 by push_cast; ring]

end
end ArtinMatthews
