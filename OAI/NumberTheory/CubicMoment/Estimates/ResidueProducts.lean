module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.CubicMoment.Estimates.ResidueIdealCharacters
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
public import OAI.NumberTheory.CubicGram.ResidueCharacters


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-! Products of the actual finite residue characters, including overlapping
moduli. The ideal coefficients are exactly the products of the two factors. -/
noncomputable section
namespace CubicFirstMoment

def residueProductLift {q r : Eisenstein} (χ : MulChar (Residues q) ℂ)
    (η : MulChar (Residues r) ℂ) (x : Eisenstein) : ℂ :=
  χ (Ideal.Quotient.mk (modulus q) x)*η (Ideal.Quotient.mk (modulus r) x)

lemma residueProductLift_congr {q r x y : Eisenstein}
    (χ : MulChar (Residues q) ℂ) (η : MulChar (Residues r) ℂ)
    (h : Ideal.Quotient.mk (modulus (q*r)) x = Ideal.Quotient.mk (modulus (q*r)) y) :
    residueProductLift χ η x = residueProductLift χ η y := by
  have hd : q*r ∣ x-y := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)
  unfold residueProductLift
  rw [residue_eq_of_dvd_sub ((dvd_mul_right q r).trans hd),
    residue_eq_of_dvd_sub ((dvd_mul_left r q).trans hd)]

lemma residueProductLift_mul {q r : Eisenstein} (χ : MulChar (Residues q) ℂ)
    (η : MulChar (Residues r) ℂ) (x y : Eisenstein) :
    residueProductLift χ η (x*y) = residueProductLift χ η x*residueProductLift χ η y := by
  simp only [residueProductLift,map_mul]
  ring

lemma residueProductLift_nonunit {q r x : Eisenstein} (χ : MulChar (Residues q) ℂ)
    (η : MulChar (Residues r) ℂ) (hx : ¬ IsUnit (Ideal.Quotient.mk (modulus (q*r)) x)) :
    residueProductLift χ η x = 0 := by
  by_cases hq : IsUnit (Ideal.Quotient.mk (modulus q) x)
  · have hr : ¬ IsUnit (Ideal.Quotient.mk (modulus r) x) := by
      intro hr
      exact hx (residue_isUnit_of_isCoprime
        ((isCoprime_of_residue_isUnit hq).mul_left (isCoprime_of_residue_isUnit hr)))
    simp only [residueProductLift,MulChar.map_nonunit η hr,mul_zero]
  · simp only [residueProductLift,MulChar.map_nonunit χ hq,zero_mul]

def productResidueChar {q r : Eisenstein} (χ : MulChar (Residues q) ℂ)
    (η : MulChar (Residues r) ℂ) : MulChar (Residues (q*r)) ℂ where
  toFun x := residueProductLift χ η (residueRepresentative (q*r) x)
  map_one' := by
    rw [residueProductLift_congr χ η (show
      Ideal.Quotient.mk (modulus (q*r)) (residueRepresentative (q*r) 1) =
      Ideal.Quotient.mk (modulus (q*r)) 1 by rw [residueRepresentative_spec,map_one])]
    simp only [residueProductLift,map_one,mul_one]
  map_mul' x y := by
    rw [residueProductLift_congr χ η (show
      Ideal.Quotient.mk (modulus (q*r)) (residueRepresentative (q*r) (x*y)) =
      Ideal.Quotient.mk (modulus (q*r))
        (residueRepresentative (q*r) x*residueRepresentative (q*r) y) by
          rw [map_mul,residueRepresentative_spec,residueRepresentative_spec,residueRepresentative_spec])]
    exact residueProductLift_mul χ η _ _
  map_nonunit' x hx := residueProductLift_nonunit χ η (by rwa [residueRepresentative_spec])

@[simp] lemma productResidueChar_mk {q r : Eisenstein} (χ : MulChar (Residues q) ℂ)
    (η : MulChar (Residues r) ℂ) (x : Eisenstein) :
    productResidueChar χ η (Ideal.Quotient.mk (modulus (q*r)) x) =
      χ (Ideal.Quotient.mk (modulus q) x)*η (Ideal.Quotient.mk (modulus r) x) :=
  residueProductLift_congr χ η (residueRepresentative_spec _ _)

lemma productResidueChar_units {q r : Eisenstein} (χ : MulChar (Residues q) ℂ)
    (η : MulChar (Residues r) ℂ)
    (hχ : ∀ u : Eisensteinˣ, χ (Ideal.Quotient.mk (modulus q) u) = 1)
    (hη : ∀ u : Eisensteinˣ, η (Ideal.Quotient.mk (modulus r) u) = 1)
    (u : Eisensteinˣ) : productResidueChar χ η (Ideal.Quotient.mk (modulus (q*r)) u) = 1 := by
  rw [productResidueChar_mk,hχ,hη,mul_one]

lemma residueIdealChar_product {q r : Eisenstein} (χ : MulChar (Residues q) ℂ)
    (η : MulChar (Residues r) ℂ) (ν : EisensteinIdealExponent) :
    residueIdealChar (q*r) (productResidueChar χ η) ν =
      residueIdealChar q χ ν*residueIdealChar r η ν := productResidueChar_mk χ η _

lemma productResidueChar_induces {q d r : Eisenstein}
    {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    (h : ResidueCharacterInduces q d χ ψ) (η : MulChar (Residues r) ℂ) :
    ResidueCharacterInduces (q*r) (d*r) (productResidueChar χ η) (productResidueChar ψ η) := by
  refine ⟨mul_dvd_mul_right h.1 r,?_⟩
  intro x hx
  rw [productResidueChar_mk,productResidueChar_mk,h.2 x hx.of_mul_left_left]

end CubicFirstMoment

end

end OAI
