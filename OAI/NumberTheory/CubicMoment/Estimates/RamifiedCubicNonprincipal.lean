module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.CubicMoment.Estimates.CubicSupplementaryPeriodicityProof
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
public import OAI.NumberTheory.CubicGram.CubeExtraction
public import OAI.NumberTheory.CubicGram.GaussCharacters
public import OAI.NumberTheory.CubicGram.Reciprocity
public import OAI.NumberTheory.CubicGram.ResidueCharacters
public import OAI.NumberTheory.CubicMoment.Estimates.CubicNumeratorOrder
public import OAI.NumberTheory.CubicMoment.Estimates.MixedCharacterSieve
public import OAI.NumberTheory.CubicMoment.Estimates.RamifiedCubicValues


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-! Nonprincipality in the unit/ramified part, detected by the primary
arguments -2 and 1+3 omega. -/
noncomputable section
namespace CubicFirstMoment

private lemma ramified_cube_of_three_dvd {u : Eisenstein} {j k : ℕ}
    (hu : u=omegaE^j ∨ u=-(omegaE^j)) (hj : 3 ∣ j) (hk : 3 ∣ k) :
    ∃ c : Eisenstein, c^3=u*lambdaE^k := by
  obtain ⟨a,rfl⟩ := hj
  obtain ⟨b,rfl⟩ := hk
  have he : omegaE^(3*a)=1 := by rw [pow_mul,omegaE_cube,one_pow]
  have hl : (lambdaE^b)^3=lambdaE^(3*b) := by rw [←pow_mul]; congr 1; omega
  rcases hu with rfl | rfl
  · exact ⟨lambdaE^b,by rw [he,one_mul,hl]⟩
  · exact ⟨-(lambdaE^b),by rw [he,neg_one_mul,neg_pow]; norm_num; exact hl⟩

private lemma unit_coprime_every (u x : Eisenstein) (hu : IsUnit u) : IsCoprime u x :=
  (isCoprime_zero_right.mpr hu).of_isCoprime_of_dvd_right (dvd_zero x)

lemma unit_ramified_cubic_nonprincipal (hpub : CubicSupplementaryPeriodicity)
    {u : Eisenstein} (hu : IsUnit u) (k : ℕ)
    (hn : ¬∃ c : Eisenstein, c^3=u*lambdaE^k) :
    cubicNumeratorChar hpub (u*lambdaE^k)
      (mul_ne_zero hu.ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero)) ≠ 1 := by
  obtain ⟨j,hj⟩ := eisenstein_unit_eq_signed_omega hu
  have hnot : ¬(3 ∣ j ∧ 3 ∣ k) := fun h => hn (ramified_cube_of_three_dvd hj h.1 h.2)
  apply (cubicNumeratorChar_ne_one_iff hpub _ _).mpr
  by_cases hj3 : 3 ∣ j
  · have hk3 : ¬3 ∣ k := fun hk => hnot ⟨hj3,hk⟩
    let x : Eisenstein := 1+3*omegaE
    have hx : primary x := primary_seven_factor
    have hval : cubicSymbol x u=1 := by
      have he : omega^(2*j)=1 :=
        (omega_primitive.pow_eq_one_iff_dvd _).mpr (dvd_mul_of_dvd_right hj3 2)
      rcases hj with rfl | rfl <;>
        simpa only [cubicSymbol_neg hx,cubicSymbol_pow_upper hx,x,
          cubicSymbol_seven_factor_omega,pow_mul] using he
    have hx9 : IsCoprime (9:Eisenstein) x := by
      convert ((primary_coprime_three hx).symm.pow_left (m := 2)) using 1
      norm_num
    refine ⟨x,hx,hx9.mul_left ((unit_coprime_every _ _ hu).mul_left
      ((primary_coprime_lambda hx).symm.pow_left)),?_⟩
    rw [cubicSymbol_mul_upper hx,hval,one_mul,cubicSymbol_pow_upper hx,
      cubicSymbol_seven_factor_lambda,←pow_mul]
    intro he
    have hd := omega_primitive.dvd_of_pow_eq_one _ he
    exact hk3 ((Nat.prime_three.dvd_mul).mp hd |>.resolve_left (by norm_num))
  · have hx := primary_neg_two
    have hx9 : IsCoprime (9:Eisenstein) (-2:Eisenstein) := by
      convert ((primary_coprime_three hx).symm.pow_left (m := 2)) using 1
      norm_num
    refine ⟨-2,hx,hx9.mul_left ((unit_coprime_every _ _ hu).mul_left
      ((primary_coprime_lambda hx).symm.pow_left)),?_⟩
    rw [cubicSymbol_mul_upper hx,cubicSymbol_pow_upper hx,
      cubicSymbol_neg_two_lambda,one_pow,mul_one]
    have he : omega^j ≠ 1 := fun h => hj3 (omega_primitive.dvd_of_pow_eq_one _ h)
    rcases hj with rfl | rfl <;>
      simpa only [cubicSymbol_neg hx,cubicSymbol_pow_upper hx,cubicSymbol_neg_two_omega] using he

end CubicFirstMoment

end

end OAI
