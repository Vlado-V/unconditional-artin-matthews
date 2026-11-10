module

public import ArtinMatthews.SourceKPDeepCongruence
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual lower unipotents and bottom-row ratios in the deep
principal congruence subgroup. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain IsLocalRing Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))

local notation "O" => P.adicCompletionIntegers K
local notation "L" => P.adicCompletion K
local notation "J₀" => sourceKPDeepIdeal K P
local notation "D₀" => sourceKPDeepIntegralGroup K P

def sourceKPDeepIdealImage : Set L := (algebraMap O L) '' (J₀ : Set O)

theorem sourceKPDeepIntegral_offDiagonal (g : D₀) (i j : Fin 2) (hij : i ≠ j) :
    g.val i j ∈ J₀ := by
  have hg : GeneralLinearGroup.map (Ideal.Quotient.mk J₀) g.val = 1 := g.property
  have he := congrArg (fun a : GL (Fin 2) (O ⧸ J₀) => a i j) hg
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change Ideal.Quotient.mk J₀ (g.val i j) = (1 : Matrix (Fin 2) (Fin 2) (O ⧸ J₀)) i j at he
  simpa only [Matrix.one_apply, ite_eq_right hij] using he

theorem sourceKPDeepIntegral_bottomRight_isUnit (g : D₀) : IsUnit (g.val 1 1) :=
  sourceKPDeepEntry_isUnit K P (g.val 1 1) (sourceKPDeepIntegral_diagonal K P g 1)

theorem sourceKPDeepLocalBase_bottomRight_ne_zero (g : D₀) :
    sourceKPDeepLocalBase K P g 1 1 ≠ 0 := by
  exact ((sourceKPDeepIntegral_bottomRight_isUnit K P g).map (algebraMap O L)).ne_zero

theorem sourceKPDeepLocalBase_bottom_ratio (g : D₀) :
    sourceKPDeepLocalBase K P g 1 0 / sourceKPDeepLocalBase K P g 1 1 ∈
      sourceKPDeepIdealImage K P := by
  let hu := sourceKPDeepIntegral_bottomRight_isUnit K P g
  let u : Oˣ := hu.unit
  have huval : (u : O) = g.val 1 1 := hu.unit_spec
  have hi : g.val 1 0 ∈ J₀ := sourceKPDeepIntegral_offDiagonal K P g 1 0 (by decide)
  refine ⟨g.val 1 0 * (u⁻¹ : Oˣ), (J₀).mul_mem_right _ hi, ?_⟩
  have hinv : algebraMap O L ((u⁻¹ : Oˣ) : O) = (algebraMap O L (u : O))⁻¹ := by
    change ((Units.map (algebraMap O L).toMonoidHom u⁻¹ : Lˣ) : L) =
      ((Units.map (algebraMap O L).toMonoidHom u : Lˣ) : L)⁻¹
    rw [map_inv, Units.val_inv_eq_inv_val]
  change algebraMap O L (g.val 1 0 * ((u⁻¹ : Oˣ) : O)) =
    algebraMap O L (g.val 1 0) / algebraMap O L (g.val 1 1)
  rw [map_mul, hinv, huval, div_eq_mul_inv]

def sourceKPIntegralLower (x : O) : GL (Fin 2) O :=
  GeneralLinearGroup.mk'' !![1, 0; x, 1] (by simp [Matrix.det_fin_two])

theorem sourceKPIntegralLower_map (x : O) :
    GeneralLinearGroup.map (algebraMap O L) (sourceKPIntegralLower K P x) =
      sourceGL2Lower (algebraMap O L x) := by
  apply GeneralLinearGroup.ext
  intro i j
  change algebraMap O L ((!![1, 0; x, 1] : Matrix (Fin 2) (Fin 2) O) i j) =
    (!![1, 0; algebraMap O L x, 1] : Matrix (Fin 2) (Fin 2) L) i j
  fin_cases i <;> fin_cases j <;> simp

def sourceKPDeepLower (x : O) (hx : x ∈ J₀) : D₀ :=
  ⟨sourceKPIntegralLower K P x, by
    change GeneralLinearGroup.map (Ideal.Quotient.mk J₀) (sourceKPIntegralLower K P x) = 1
    have hx0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
    apply GeneralLinearGroup.ext
    intro i j
    change Ideal.Quotient.mk J₀ ((!![1, 0; x, 1] : Matrix (Fin 2) (Fin 2) O) i j) =
      (1 : Matrix (Fin 2) (Fin 2) (O ⧸ J₀)) i j
    fin_cases i <;> fin_cases j <;> simp [hx0]⟩

theorem sourceKPDeepLocalBase_lower (x : O) (hx : x ∈ J₀) :
    sourceKPDeepLocalBase K P (sourceKPDeepLower K P x hx) = sourceGL2Lower (algebraMap O L x) :=
  sourceKPIntegralLower_map K P x

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPDeepLocalSection_lower (x : O) (hx : x ∈ J₀) :
    sourceKPDeepLocalSection K P hζ (sourceKPDeepLower K P x hx) =
      sourceFiniteKP2Lift K hζ P (sourceGL2Lower (algebraMap O L x)) := by
  apply SourceFiniteKP2Cover.ext
  · rfl
  · exact sourceKPDeepLocalBase_lower K P x hx

end
end ArtinMatthews
