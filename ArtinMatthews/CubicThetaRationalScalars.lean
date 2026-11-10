module

public import ArtinMatthews.CubicReciprocityNonprincipalCharacterBase
public import ArtinMatthews.CubicReciprocityNonprincipalConjugationModel
public import ArtinMatthews.CubicReciprocityNonprincipalConjugation
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
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual anticyclotomic cubic character is trivial on invertible
rational scalars, as required by its scalar congruence transformation. -/
noncomputable section
namespace ArtinMatthews

open OAI OAI.SevenEighths
local notation "EO" => HeckeFamily.O

/-- A fixed point of conjugation has trivial nonzero cubic character value. -/
theorem cubicNumeratorHeckeCharacter_residue_fixed (A : ℤ) (hA : A ≠ 0)
    (x : EO ⧸ cubicNumeratorHeckeModulus A) (hx : IsUnit x)
    (hfixed : cubicNumeratorResidueConjugation A x = x) :
    (cubicNumeratorHeckeCharacter A hA).residue x = 1 := by
  let z := cubicNumeratorHeckeResidue A hA x
  have h3 : z ^ 3 = 1 := by
    have h := congrArg (fun χ : MulChar (EO ⧸ cubicNumeratorHeckeModulus A) ℂ => χ x)
      (cubicNumeratorHeckeResidue_cube A hA)
    simpa only [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), MulChar.one_apply hx]
      using h
  have hz : z ≠ 0 := by
    intro hz
    simp [hz] at h3
  have hinv : z = z⁻¹ := by
    have h := cubicNumeratorHeckeCharacter_residue_conjugate_inv A hA x
    change cubicNumeratorHeckeResidue A hA (cubicNumeratorResidueConjugation A x) =
      (cubicNumeratorHeckeResidue A hA x)⁻¹ at h
    rw [hfixed] at h
    exact h
  have h2 : z ^ 2 = 1 := by
    calc
      z ^ 2 = z * z := pow_two z
      _ = z * z⁻¹ := congrArg (fun t : ℂ => z * t) hinv
      _ = 1 := mul_inv_cancel₀ hz
  change z = 1
  simpa only [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, h2, one_mul] using h3

/-- Rational residue units are fixed by conjugation, hence have value one. -/
theorem cubicNumeratorHeckeCharacter_residue_int (A : ℤ) (hA : A ≠ 0)
    (d : ℤ) (hd : IsUnit (d : EO ⧸ cubicNumeratorHeckeModulus A)) :
    (cubicNumeratorHeckeCharacter A hA).residue (d : EO ⧸ cubicNumeratorHeckeModulus A) =
      1 :=
  cubicNumeratorHeckeCharacter_residue_fixed A hA _ hd (map_intCast _ d)

/-- Multiplication by an invertible rational scalar preserves every residue
weight, including zero weights. -/
theorem cubicNumeratorHeckeCharacter_residue_int_mul (A : ℤ) (hA : A ≠ 0)
    (d : ℤ) (hd : IsUnit (d : EO ⧸ cubicNumeratorHeckeModulus A))
    (x : EO ⧸ cubicNumeratorHeckeModulus A) :
    (cubicNumeratorHeckeCharacter A hA).residue ((d : EO ⧸ cubicNumeratorHeckeModulus A) * x) =
      (cubicNumeratorHeckeCharacter A hA).residue x := by
  change cubicNumeratorHeckeResidue A hA ((d : EO ⧸ cubicNumeratorHeckeModulus A) * x) = _
  rw [map_mul]
  exact (congrArg (fun z : ℂ => z * cubicNumeratorHeckeResidue A hA x)
    (cubicNumeratorHeckeCharacter_residue_int A hA d hd)).trans (one_mul _)

/-- The same invariance holds for the actual integral theta coefficient. -/
theorem cubicNumeratorHeckeCharacter_element_int_mul (A : ℤ) (hA : A ≠ 0)
    (d : ℤ) (hd : IsUnit (d : EO ⧸ cubicNumeratorHeckeModulus A)) (x : EO) :
    HeckeFamily.elementCoeff (cubicNumeratorHeckeCharacter A hA) ((d : EO) * x) =
      HeckeFamily.elementCoeff (cubicNumeratorHeckeCharacter A hA) x := by
  unfold HeckeFamily.elementCoeff
  rw [map_mul, map_intCast]
  exact cubicNumeratorHeckeCharacter_residue_int_mul A hA d hd _

end ArtinMatthews
