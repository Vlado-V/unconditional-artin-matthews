module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.CubicMoment.Estimates.PrimitiveConductor
public import OAI.NumberTheory.CubicMoment.Estimates.MixedResidueCharacters
public import OAI.NumberTheory.CubicMoment.Estimates.PrimaryHeckeCharacter
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
public import OAI.NumberTheory.CubicMoment.Estimates.MixedCharacterSieve


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-! Nonprincipality of the actual mixed character. The zero-frequency
Gauss identity and an explicit primary Chinese-remainder lift supply the
witness; nonprincipality is not imposed as an extra hypothesis. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma exists_primary_residue_lift {q : Eisenstein} (hq : primary q) (y : Eisenstein) :
    ∃ x : Eisenstein, primary x ∧
      Ideal.Quotient.mk (modulus q) x = Ideal.Quotient.mk (modulus q) y := by
  obtain ⟨u,v,huv⟩ := (primary_coprime_three hq)
  refine ⟨q*u+3*v*y,?_,?_⟩
  · refine ⟨v*(y-1),?_⟩
    linear_combination huv
  · apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_singleton.mpr
    refine ⟨u*(1-y),?_⟩
    linear_combination y*huv

lemma mixedResidueChar_ne_one {a b : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hnu : ¬ IsUnit (a*b)) :
    mixedResidueChar a b ha hb ≠ 1 := by
  let : Finite (Residues (a*b)) := finite_residues (mul_ne_zero (primary_ne_zero ha) (primary_ne_zero hb))
  let : Fintype (Residues (a*b)) := Fintype.ofFinite _
  have hz : mixedCubic a b 0 = 0 := by
    apply mixedCubic_eq_zero_of_nonunit ha hb
    intro h
    exact hnu (isCoprime_zero_right.mp (isCoprime_of_residue_isUnit h))
  have hsum := mixedResidueChar_fourier ha hb hsa hsb hab (0:Eisenstein)
  simp [huxleyPhase,hz] at hsum
  intro he
  rw [he,MulChar.sum_one_eq_card_units] at hsum
  exact (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero) :
    (Fintype.card (Residues (a*b))ˣ : ℂ) ≠ 0) hsum

/-- A primary witness for nonprincipality, on the actual prime-to-conductor
ideal character used in the finite-order Hecke input. -/
theorem mixedCubic_nonprincipal {a b : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hnu : ¬ IsUnit (a*b)) : MixedCubicNonprincipal a b := by
  let χ := mixedResidueChar a b ha hb
  obtain ⟨v,hv⟩ := MulChar.ne_one_iff.mp (mixedResidueChar_ne_one ha hb hsa hsb hab hnu)
  obtain ⟨y,hy⟩ := Ideal.Quotient.mk_surjective (v : Residues (a*b))
  obtain ⟨x,hx,hxy⟩ := exists_primary_residue_lift (primary_mul ha hb) y
  have hres : Ideal.Quotient.mk (modulus (a*b)) x = v := hxy.trans hy
  have hcx : IsCoprime (a*b) x := isCoprime_of_residue_isUnit (by rw [hres]; exact v.isUnit)
  refine ⟨x,hx,hcx,?_⟩
  intro he
  apply hv
  change mixedResidueChar a b ha hb v = 1
  rw [← hres,mixedResidueChar_mk]
  exact he

lemma primaryMixedResidueChar_witness {a b : Eisenstein}
    (ha : primary a) (hb : primary b) (h : MixedCubicNonprincipal a b) :
    ∃ x : Eisenstein, IsCoprime (3*(a*b)) x ∧
      primaryMixedResidueChar a b ha hb (Ideal.Quotient.mk (modulus (3*(a*b))) x) ≠ 1 := by
  obtain ⟨x,hx,hcop,hne⟩ := h
  refine ⟨x,(primary_coprime_three hx).symm.mul_left hcop,?_⟩
  rwa [primaryMixedResidueChar_primary ha hb hx]

/-- The actual nonprincipal primitive character inducing the mixed cubic
symbol, with the exact norm and unit-invariance guarantees needed by the
published Hecke functional equation. -/
theorem mixed_primitive_conductor {a b : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hnu : ¬ IsUnit (a*b)) :
    ∃ (d : Eisenstein) (ψ : MulChar (Residues d) ℂ),
      d ≠ 0 ∧ PrimitiveResidueCharacter d ψ ∧ ψ ≠ 1 ∧
      normNat d ≤ normNat (3*(a*b)) ∧
      (∀ u : Eisensteinˣ, ψ (Ideal.Quotient.mk (modulus d) u) = 1) ∧
      ResidueCharacterInduces (3*(a*b)) d (primaryMixedResidueChar a b ha hb) ψ ∧
      (∀ x : Eisenstein, primary x → IsCoprime (a*b) x →
        ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x) := by
  have hq : 3*(a*b) ≠ (0:Eisenstein) :=
    mul_ne_zero (by norm_num) (mul_ne_zero (primary_ne_zero ha) (primary_ne_zero hb))
  obtain ⟨d,ψ,hd,hind,hN,hprim⟩ := primitive_residue_conductor_exists hq
    (primaryMixedResidueChar a b ha hb)
  have hw := primaryMixedResidueChar_witness ha hb
    (mixedCubic_nonprincipal ha hb hsa hsb hab hnu)
  refine ⟨d,ψ,hd,hprim,hind.nonprincipal hw,hN,
    hind.global_units (primaryMixedResidueChar_trivialInfinity ha hb),hind,?_⟩
  intro x hx hcop
  exact (hind.2 x ((primary_coprime_three hx).symm.mul_left hcop)).trans
    (primaryMixedResidueChar_primary ha hb hx)

end CubicFirstMoment

end

end OAI
