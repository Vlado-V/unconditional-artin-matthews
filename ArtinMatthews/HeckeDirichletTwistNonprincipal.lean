module

public import ArtinMatthews.HeckeDirichletTwist
public import ArtinMatthews.CubicReciprocityNonprincipalCharacterBase
public import ArtinMatthews.CubicReciprocityNonprincipalCharacter
public import ArtinMatthews.CubicReciprocityNonprincipalConjugation
public import ArtinMatthews.CubicThetaUnitLiftNorm
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

/-! Dirichlet norm twists of actual nontrivial cubic anticyclotomic
characters remain nonprincipal. The proof detects a norm-one residue unit,
so it does not require any analytic nonvanishing input. -/

noncomputable section
namespace ArtinMatthews

open OAI OAI.SevenEighths
local notation "EO" => HeckeFamily.O

theorem heckeResidueNorm_factor_of_norm_one {M q : ℕ} [NeZero M] [NeZero q]
    (hMq : cubicThetaRationalModulus M ≤ cubicThetaRationalModulus q)
    (r : CubicThetaResidue M) (hr : r*cubicThetaResidueConjugation M r = 1) :
    heckeResidueNorm q (Ideal.Quotient.factor hMq r) = 1 := by
  let g : CubicThetaResidue M →+* CubicThetaResidue q := Ideal.Quotient.factor hMq
  have hgκ (s : CubicThetaResidue M) :
      g (cubicThetaResidueConjugation M s) = cubicThetaResidueConjugation q (g s) := by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective s
    rw [cubicThetaResidueConjugation_mk]
    change Ideal.Quotient.mk (cubicThetaRationalModulus q) (heckeIntegerConjugation z) =
      cubicThetaResidueConjugation q (Ideal.Quotient.mk (cubicThetaRationalModulus q) z)
    exact (cubicThetaResidueConjugation_mk q z).symm
  apply heckeNormScalar_injective q
  change heckeNormScalar q (heckeResidueNormValue q (g r)) = heckeNormScalar q 1
  rw [heckeResidueNormValue_scalar, map_one, ← hgκ, ← map_mul, hr, map_one]

theorem heckeDirichletTwist_nonprincipal_of_norm_one
    (η : HeckeFamily.Character) {M q : ℕ} [NeZero M] [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (hMη : cubicThetaRationalModulus M ≤ η.modulus)
    (hMq : cubicThetaRationalModulus M ≤ cubicThetaRationalModulus q)
    (u : (CubicThetaResidue M)ˣ)
    (huNorm : (u : CubicThetaResidue M)*cubicThetaResidueConjugation M u = 1)
    (huη : η.residue (Ideal.Quotient.factor hMη u) ≠ 1) :
    (heckeDirichletTwist η χ).residue ≠ 1 := by
  let f : CubicThetaResidue M →+* (EO ⧸ η.modulus) := Ideal.Quotient.factor hMη
  let g : CubicThetaResidue M →+* CubicThetaResidue q := Ideal.Quotient.factor hMq
  let t : CubicThetaResidue M →+* (EO ⧸ (heckeDirichletTwist η χ).modulus) :=
    Ideal.Quotient.factor (le_inf hMη hMq)
  have hvalue (r : CubicThetaResidue M) :
      (heckeDirichletTwist η χ).residue (t r) = η.residue (f r) * χ (heckeResidueNorm q (g r)) := by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective r
    change HeckeFamily.elementCoeff (heckeDirichletTwist η χ) z =
      HeckeFamily.elementCoeff η z * χ (heckeResidueNorm q
        (Ideal.Quotient.mk (cubicThetaRationalModulus q) z))
    rw [heckeDirichletTwist_elementCoeff, heckeResidueNorm_mk]
  have hnorm : heckeResidueNorm q (g u) = 1 :=
    heckeResidueNorm_factor_of_norm_one hMq u huNorm
  intro hprincipal
  apply huη
  have htunit : IsUnit (t (u : CubicThetaResidue M)) := u.isUnit.map t
  have hv := hvalue (u : CubicThetaResidue M)
  rw [hprincipal, MulChar.one_apply htunit, hnorm, map_one, mul_one] at hv
  exact hv.symm

theorem heckeAnticyclotomic_norm_one_unit
    (η : HeckeFamily.Character) (κ : (EO ⧸ η.modulus) ≃+* (EO ⧸ η.modulus))
    (hκ : ∀ z : EO, κ (Ideal.Quotient.mk η.modulus z) =
      Ideal.Quotient.mk η.modulus (heckeIntegerConjugation z))
    (hanti : ∀ v : (EO ⧸ η.modulus)ˣ, η.residue (κ v) = (η.residue v)⁻¹)
    (hcubic : η.residue ^ 3 = 1) (hne : η.residue ≠ 1)
    (M : ℕ) [NeZero M] (hMη : cubicThetaRationalModulus M ≤ η.modulus) :
    ∃ u : (CubicThetaResidue M)ˣ,
      (u : CubicThetaResidue M)*cubicThetaResidueConjugation M u = 1 ∧
      η.residue (Ideal.Quotient.factor hMη u) ≠ 1 := by
  let f : CubicThetaResidue M →+* (EO ⧸ η.modulus) := Ideal.Quotient.factor hMη
  have hcompat (r : CubicThetaResidue M) :
      f (cubicThetaResidueConjugation M r) = κ (f r) := by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact (hκ z).symm
  have hneUnits : η.residue.toMonoidHom.comp (Units.coeHom (EO ⧸ η.modulus)) ≠ 1 := by
    intro heq
    apply hne
    apply MulChar.ext
    intro v
    have hv := congrArg (fun ψ : (EO ⧸ η.modulus)ˣ →* ℂ => ψ v) heq
    simpa using hv
  have hcubeUnits (v : (EO ⧸ η.modulus)ˣ) : η.residue v ^ 3 = 1 := by
    have h := congrArg (fun ψ : MulChar (EO ⧸ η.modulus) ℂ => ψ v) hcubic
    simpa only [MulChar.pow_apply_coe, MulChar.one_apply_coe] using h
  exact finite_ring_norm_one_unit_nontrivial
    f (Ideal.Quotient.factor_surjective hMη) (cubicThetaResidueConjugation M) κ
    (cubicThetaResidueConjugation_involutive M) hcompat η.residue.toMonoidHom
    hanti hcubeUnits hneUnits

theorem heckeDirichletTwist_nonprincipal
    (η : HeckeFamily.Character) (κ : (EO ⧸ η.modulus) ≃+* (EO ⧸ η.modulus))
    (hκ : ∀ z : EO, κ (Ideal.Quotient.mk η.modulus z) =
      Ideal.Quotient.mk η.modulus (heckeIntegerConjugation z))
    (hanti : ∀ v : (EO ⧸ η.modulus)ˣ, η.residue (κ v) = (η.residue v)⁻¹)
    (hcubic : η.residue ^ 3 = 1) (hne : η.residue ≠ 1)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    (heckeDirichletTwist η χ).residue ≠ 1 := by
  let M := η.period*q
  have hM0 : M ≠ 0 := Nat.mul_ne_zero (NeZero.ne η.period) (NeZero.ne q)
  let : NeZero M := ⟨hM0⟩
  have hMη : cubicThetaRationalModulus M ≤ η.modulus := by
    apply Ideal.span_le.mpr
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    change ((η.period*q : ℕ) : EO) ∈ η.modulus
    rw [Nat.cast_mul]
    exact η.modulus.mul_mem_right (q : EO) η.period_mem
  have hMq : cubicThetaRationalModulus M ≤ cubicThetaRationalModulus q := by
    apply Ideal.span_le.mpr
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    apply Ideal.mem_span_singleton.mpr
    refine ⟨(η.period : EO), ?_⟩
    simp only [M, Nat.cast_mul, mul_comm]
  obtain ⟨u, huNorm, huη⟩ := heckeAnticyclotomic_norm_one_unit η κ hκ hanti hcubic hne M hMη
  exact heckeDirichletTwist_nonprincipal_of_norm_one η χ hMη hMq u huNorm huη

theorem cubicNumeratorHeckeDirichletTwist_nonprincipal (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y^3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    (heckeDirichletTwist (cubicNumeratorHeckeCharacter A hA) χ).residue ≠ 1 := by
  exact heckeDirichletTwist_nonprincipal (cubicNumeratorHeckeCharacter A hA)
    (cubicNumeratorResidueConjugation A)
    (cubicNumeratorResidueConjugation_mk A)
    (fun v => cubicNumeratorHeckeCharacter_residue_conjugate_inv A hA
      (v : EO ⧸ (cubicNumeratorHeckeCharacter A hA).modulus))
    (cubicNumeratorHeckeCharacter_cube A hA)
    (cubicNumeratorHeckeCharacter_nonprincipal A hA hnoncube) χ

end ArtinMatthews
