module

public import ArtinMatthews.HeckeDirichletProduct
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The literal finite family of primitive characters of positive
conductor at most Q, including its conductor-one member. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev IdealPrimitiveCharacters (Q : ℕ) :=
  (q : ↥(Icc 1 Q)) × {χ : DirichletCharacter ℂ q.val // χ.IsPrimitive}

def idealPrimitiveCharacterValue {Q : ℕ} (χ : IdealPrimitiveCharacters Q) (n : ℕ) : ℂ :=
  χ.2.val (n:ZMod χ.1.val)

theorem idealPrimitiveCharacter_level_pos {Q : ℕ} (χ : IdealPrimitiveCharacters Q) :
    0<χ.1.val := lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp χ.1.property).1

theorem idealPrimitiveCharacters_card_le (Q : ℕ) :
    Fintype.card (IdealPrimitiveCharacters Q)≤Q^2 := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑q : ↥(Icc 1 Q),Fintype.card (DirichletCharacter ℂ q.val) := by
      apply sum_le_sum
      intro q _
      exact Fintype.card_le_of_injective (fun χ : {χ : DirichletCharacter ℂ q.val // χ.IsPrimitive} => χ.val)
        Subtype.val_injective
    _ = ∑q : ↥(Icc 1 Q),q.val.totient := by
      apply sum_congr rfl
      intro q _
      let : NeZero q.val := ⟨by have hq := (mem_Icc.mp q.property).1; omega⟩
      exact Nat.card_eq_fintype_card.symm.trans (DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q.val)
    _ ≤ ∑_q : ↥(Icc 1 Q),Q := by
      apply sum_le_sum
      intro q _
      exact (Nat.totient_le q.val).trans (mem_Icc.mp q.property).2
    _ = Q^2 := by simp [pow_two]

theorem idealPrimitiveCharacter_lifts_injective {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive)
    (h : χ.changeLevel (dvd_mul_right q r)=ψ.changeLevel (dvd_mul_left r q)) :
    q=r ∧ HEq χ ψ := by
  have hq : q=r := calc
    q = χ.conductor := hχ.symm
    _ = (χ.changeLevel (dvd_mul_right q r)).conductor := (χ.conductor_changeLevel _).symm
    _ = (ψ.changeLevel (dvd_mul_left r q)).conductor := congrArg DirichletCharacter.conductor h
    _ = ψ.conductor := ψ.conductor_changeLevel _
    _ = r := hψ
  subst r
  refine ⟨rfl,heq_of_eq ?_⟩
  exact (DirichletCharacter.changeLevel_injective (dvd_mul_right q q)) h

theorem idealPrimitiveCharacters_product_nonprincipal {Q : ℕ}
    (χ ψ : IdealPrimitiveCharacters Q) (hne : χ≠ψ) :
    heckeDirichletProduct (star χ.2.val) ψ.2.val≠1 := by
  let : NeZero χ.1.val := ⟨(idealPrimitiveCharacter_level_pos χ).ne'⟩
  let : NeZero ψ.1.val := ⟨(idealPrimitiveCharacter_level_pos ψ).ne'⟩
  intro hp
  have hprod : (χ.2.val.changeLevel (dvd_mul_right χ.1.val ψ.1.val))⁻¹ *
      ψ.2.val.changeLevel (dvd_mul_left ψ.1.val χ.1.val)=1 := by
    simpa only [heckeDirichletProduct,MulChar.star_eq_inv,map_inv] using hp
  have hlift := idealPrimitiveCharacter_lifts_injective χ.2.val ψ.2.val χ.2.property ψ.2.property
    (inv_mul_eq_one.mp hprod)
  obtain ⟨q,χ⟩ := χ
  obtain ⟨r,ψ⟩ := ψ
  have hqr : q=r := Subtype.ext hlift.1
  subst r
  have hχψ : χ=ψ := Subtype.ext (eq_of_heq hlift.2)
  exact hne (by cases hχψ; rfl)

theorem idealPrimitiveCharacterValue_norm_le {Q : ℕ} (χ : IdealPrimitiveCharacters Q) (n : ℕ) :
    ‖idealPrimitiveCharacterValue χ n‖≤1 := χ.2.val.norm_le_one _

end
end ArtinMatthews
