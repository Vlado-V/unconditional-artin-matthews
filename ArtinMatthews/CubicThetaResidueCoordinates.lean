module

public import ArtinMatthews.CubicReciprocityNonprincipalConjugationModel
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import OAI.NumberTheory.DirichletL.Hecke.Coordinates


set_option backward.privateInPublic true
@[expose] public section

/-! Actual two-coordinate parametrization of the Eisenstein residue ring `(M)`. -/

noncomputable section

namespace ArtinMatthews

open OAI OAI.SevenEighths
open scoped BigOperators

local notation "EO" => HeckeFamily.O

def cubicThetaRationalModulus (M : ℕ) : Ideal EO := Ideal.span {(M : EO)}

theorem cubicThetaRationalModulus_ne_bot (M : ℕ) [NeZero M] :
    cubicThetaRationalModulus M ≠ ⊥ := by
  apply Ideal.span_singleton_eq_bot.not.mpr
  exact Nat.cast_ne_zero.mpr (NeZero.ne M)

abbrev CubicThetaResidue (M : ℕ) := EO ⧸ cubicThetaRationalModulus M

instance cubicThetaResidueFinite (M : ℕ) [NeZero M] : Finite (CubicThetaResidue M) :=
  Ring.HasFiniteQuotients.finiteQuotient (cubicThetaRationalModulus_ne_bot M)

instance cubicThetaResidueFintype (M : ℕ) [NeZero M] : Fintype (CubicThetaResidue M) :=
  Fintype.ofFinite _

def cubicThetaIntResidueHom (M : ℕ) : ℤ →+ CubicThetaResidue M :=
  (Ideal.Quotient.mk (cubicThetaRationalModulus M)).toAddMonoidHom.comp (Int.castAddHom EO)

def cubicThetaZModResidueHom (M : ℕ) : ZMod M →+ CubicThetaResidue M :=
  ZMod.lift M ⟨cubicThetaIntResidueHom M, by
    change Ideal.Quotient.mk (cubicThetaRationalModulus M) ((M : ℤ) : EO) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (by simp)⟩

@[simp] theorem cubicThetaZModResidueHom_intCast (M : ℕ) (a : ℤ) :
    cubicThetaZModResidueHom M (a : ZMod M) =
      Ideal.Quotient.mk (cubicThetaRationalModulus M) (a : EO) :=
  ZMod.lift_coe _ _ _

def cubicThetaCoordinateHom (M : ℕ) :
    (ZMod M × ZMod M) →+ CubicThetaResidue M where
  toFun p := cubicThetaZModResidueHom M p.1 + cubicThetaZModResidueHom M p.2 *
    Ideal.Quotient.mk (cubicThetaRationalModulus M) HeckeFamily.omega
  map_zero' := by simp
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, map_add]; ring

@[simp] theorem cubicThetaCoordinateHom_intCast (M : ℕ) (a b : ℤ) :
    cubicThetaCoordinateHom M (a, b) = Ideal.Quotient.mk (cubicThetaRationalModulus M)
      (HeckeFamily.coordinateElement a b) := by
  simp only [cubicThetaCoordinateHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    cubicThetaZModResidueHom_intCast, HeckeFamily.coordinateElement, map_add, map_mul]

theorem cubicThetaCoordinateHom_surjective (M : ℕ) :
    Function.Surjective (cubicThetaCoordinateHom M) := by
  intro x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨⟨a, b⟩, hab⟩ := HeckeCoordinates.coordinateElement_surjective z
  change HeckeFamily.coordinateElement a b = z at hab
  exact ⟨(a, b), by rw [cubicThetaCoordinateHom_intCast, hab]⟩

theorem cubicThetaResidue_card (M : ℕ) [NeZero M] :
    Fintype.card (CubicThetaResidue M) = M ^ 2 := by
  have hrank : Module.finrank ℤ EO = 2 := by
    rw [NumberField.RingOfIntegers.rank HeckeFamily.K,
      IsCyclotomicExtension.Rat.finrank 3 HeckeFamily.K]
    decide
  rw [← Nat.card_eq_fintype_card]
  change (cubicThetaRationalModulus M).absNorm = _
  rw [cubicThetaRationalModulus, Ideal.absNorm_span_natCast, hrank]

theorem cubicThetaCoordinateHom_bijective (M : ℕ) [NeZero M] :
    Function.Bijective (cubicThetaCoordinateHom M) := by
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  refine ⟨cubicThetaCoordinateHom_surjective M, ?_⟩
  rw [Fintype.card_prod, ZMod.card, cubicThetaResidue_card]
  ring

def cubicThetaCoordinateEquiv (M : ℕ) [NeZero M] :
    (ZMod M × ZMod M) ≃ CubicThetaResidue M :=
  Equiv.ofBijective (cubicThetaCoordinateHom M) (cubicThetaCoordinateHom_bijective M)

@[simp] theorem cubicThetaCoordinateEquiv_intCast (M : ℕ) [NeZero M] (a b : ℤ) :
    cubicThetaCoordinateEquiv M (a, b) = Ideal.Quotient.mk (cubicThetaRationalModulus M)
      (HeckeFamily.coordinateElement a b) :=
  cubicThetaCoordinateHom_intCast M a b

def cubicThetaResidueConjugation (M : ℕ) : CubicThetaResidue M ≃+* CubicThetaResidue M :=
  Ideal.quotientEquiv _ _ heckeIntegerConjugation (by
    simp only [cubicThetaRationalModulus, Ideal.map_span, Set.image_singleton, map_natCast])

@[simp] theorem cubicThetaResidueConjugation_mk (M : ℕ) (x : EO) :
    cubicThetaResidueConjugation M (Ideal.Quotient.mk (cubicThetaRationalModulus M) x) =
      Ideal.Quotient.mk (cubicThetaRationalModulus M) (heckeIntegerConjugation x) := rfl

theorem cubicThetaResidueConjugation_involutive (M : ℕ) :
    Function.Involutive (cubicThetaResidueConjugation M) := by
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [cubicThetaResidueConjugation_mk, heckeIntegerConjugation_involutive]

end ArtinMatthews
