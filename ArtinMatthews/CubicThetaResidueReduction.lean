module

public import ArtinMatthews.CubicThetaResidueCoordinates
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

/-! Reduction from an enlarged rational modulus and exact periodic weights. -/

noncomputable section
namespace ArtinMatthews

open OAI OAI.SevenEighths

local notation "EO" => HeckeFamily.O

theorem cubicThetaRationalModulus_le (A : ℤ) (M : ℕ)
    (hdiv : 9 * A ∣ (M : ℤ)) :
    cubicThetaRationalModulus M ≤ cubicNumeratorHeckeModulus A := by
  apply Ideal.span_le.mpr
  intro x hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  apply Ideal.mem_span_singleton.mpr
  obtain ⟨d, hd⟩ := hdiv
  refine ⟨(d : EO), ?_⟩
  exact_mod_cast hd

def cubicThetaResidueReduction (A : ℤ) (M : ℕ) (hdiv : 9 * A ∣ (M : ℤ)) :
    CubicThetaResidue M →+* (EO ⧸ cubicNumeratorHeckeModulus A) :=
  Ideal.Quotient.factor (cubicThetaRationalModulus_le A M hdiv)

theorem cubicThetaResidueReduction_surjective (A : ℤ) (M : ℕ)
    (hdiv : 9 * A ∣ (M : ℤ)) :
    Function.Surjective (cubicThetaResidueReduction A M hdiv) :=
  Ideal.Quotient.factor_surjective _

@[simp] theorem cubicThetaResidueReduction_mk (A : ℤ) (M : ℕ)
    (hdiv : 9 * A ∣ (M : ℤ)) (x : EO) :
    cubicThetaResidueReduction A M hdiv
      (Ideal.Quotient.mk (cubicThetaRationalModulus M) x) =
      Ideal.Quotient.mk (cubicNumeratorHeckeModulus A) x := rfl

theorem cubicThetaResidueReduction_conjugate (A : ℤ) (M : ℕ)
    (hdiv : 9 * A ∣ (M : ℤ)) (x : CubicThetaResidue M) :
    cubicThetaResidueReduction A M hdiv (cubicThetaResidueConjugation M x) =
      cubicNumeratorResidueConjugation A (cubicThetaResidueReduction A M hdiv x) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

def cubicThetaCoordinateWeight (χ : HeckeFamily.Character) (M : ℕ)
    (r : Fin M × Fin M) : ℂ :=
  HeckeFamily.elementCoeff χ (HeckeFamily.coordinateElement r.1 r.2)

/-- Every rational multiple of the character modulus is a valid coordinate
period; it need not equal the period chosen by the constructor. -/
theorem cubicThetaCoordinateWeight_periodicCoeff (χ : HeckeFamily.Character)
    (M : ℕ) [NeZero M] (hM : (M : EO) ∈ χ.modulus) (n : ℤ × ℤ) :
    HeckeTheta.periodicCoeff (cubicThetaCoordinateWeight χ M) n =
      HeckeFamily.elementCoeff χ (HeckeFamily.coordinateElement n.1 n.2) := by
  obtain ⟨p, rfl⟩ := (HeckeTheta.residueEquiv M).symm.surjective n
  simp only [HeckeTheta.periodicCoeff, Equiv.apply_symm_apply, cubicThetaCoordinateWeight]
  change HeckeFamily.elementCoeff χ (HeckeFamily.coordinateElement p.1.1 p.1.2) =
    HeckeFamily.elementCoeff χ (HeckeFamily.coordinateElement
      (p.2.1 * (M : ℤ) + p.1.1) (p.2.2 * (M : ℤ) + p.1.2))
  have heq : HeckeFamily.coordinateElement
      (p.2.1 * (M : ℤ) + p.1.1) (p.2.2 * (M : ℤ) + p.1.2) =
      HeckeFamily.coordinateElement p.1.1 p.1.2 + (M : EO) *
        ((p.2.1 : EO) + (p.2.2 : EO) * HeckeFamily.omega) := by
    unfold HeckeFamily.coordinateElement
    push_cast
    ring
  rw [heq]
  unfold HeckeFamily.elementCoeff
  rw [map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hM, zero_mul, add_zero]

end ArtinMatthews
