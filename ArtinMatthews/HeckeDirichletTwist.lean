module

public import ArtinMatthews.HeckeDirichletNormCharacter
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import OAI.NumberTheory.DirichletL.ConductorBounds
public import OAI.NumberTheory.DirichletL.PrimeRows.NormFiberExtraction


set_option backward.privateInPublic true
@[expose] public section

/-! Actual Dirichlet twisting of the Eisenstein Hecke family, with its
literal ideal coefficients and quadratic modulus bound. -/

noncomputable section
namespace ArtinMatthews

open OAI OAI.SevenEighths
local notation "EO" => HeckeFamily.O

def heckeDirichletTwist (η : HeckeFamily.Character) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) : HeckeFamily.Character :=
  HeckeFamily.Character.ofResidue (η.modulus ⊓ (heckeDirichletNormCharacter χ).modulus)
    (Ideal.inf_ne_bot_of_ne_bot η.modulus_ne_bot (heckeDirichletNormCharacter χ).modulus_ne_bot)
    (ResidueCharacter.product _ _ η.residue (heckeDirichletNormCharacter χ).residue)
    (ResidueCharacter.product_global_units _ _ _ _ η.unit_trivial
      (heckeDirichletNormCharacter χ).unit_trivial)

theorem heckeDirichletTwist_elementCoeff (η : HeckeFamily.Character) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (z : EO) :
    HeckeFamily.elementCoeff (heckeDirichletTwist η χ) z =
      HeckeFamily.elementCoeff η z * χ ((Ideal.span {z}).absNorm : ZMod q) := by
  have h := ResidueCharacter.product_mk η.modulus (heckeDirichletNormCharacter χ).modulus
    η.residue (heckeDirichletNormCharacter χ).residue z
  change HeckeFamily.elementCoeff (heckeDirichletTwist η χ) z =
    HeckeFamily.elementCoeff η z * HeckeFamily.elementCoeff (heckeDirichletNormCharacter χ) z at h
  rwa [heckeDirichletNormCharacter_elementCoeff] at h

theorem heckeDirichletTwist_idealCoeff (η : HeckeFamily.Character) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (I : Ideal EO) :
    thetaIdealCharacter (heckeDirichletTwist η χ) I =
      thetaIdealCharacter η I * χ (I.absNorm : ZMod q) := by
  have h : thetaIdealCharacter (heckeDirichletTwist η χ) I =
      thetaIdealCharacter η I * thetaIdealCharacter (heckeDirichletNormCharacter χ) I :=
    IdealCharacter.ofResidue_product _ _ _ _ _ _ I
  rw [h]
  by_cases hI : I = 0
  · subst I
    simp only [map_zero, zero_mul]
  · rw [heckeDirichletNormCharacter_idealCoeff χ I hI]

theorem heckeDirichletTwist_modulus_norm (η : HeckeFamily.Character) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    (heckeDirichletTwist η χ).modulus.absNorm ≤ η.modulus.absNorm*q^2 := by
  let : Finite (EO ⧸ η.modulus) := Ring.HasFiniteQuotients.finiteQuotient η.modulus_ne_bot
  let : Finite (EO ⧸ (heckeDirichletNormCharacter χ).modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient (heckeDirichletNormCharacter χ).modulus_ne_bot
  have h := FiniteConductor.absNorm_inf_le_mul η.modulus (heckeDirichletNormCharacter χ).modulus
  change (heckeDirichletTwist η χ).modulus.absNorm ≤
    η.modulus.absNorm * (heckeDirichletNormCharacter χ).modulus.absNorm at h
  rwa [heckeDirichletNormCharacter_modulus_norm] at h

theorem idealThetaCoeff_heckeDirichletTwist (η : HeckeFamily.Character) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (n : ℕ) :
    idealThetaCoeff (heckeDirichletTwist η χ) n = idealThetaCoeff η n * χ n := by
  unfold idealThetaCoeff
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro I hI
  rw [heckeDirichletTwist_idealCoeff, mem_idealsOfNorm.mp hI]

end ArtinMatthews
