module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.CubicMoment.Estimates.CubicNumeratorCharacter
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
public import OAI.NumberTheory.CubicGram.CubeExtraction
public import OAI.NumberTheory.CubicMoment.Estimates.CoprimeResidueLift
public import OAI.NumberTheory.CubicMoment.Estimates.CubicNumeratorOrder


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-! Multiplication by a nonzero cube changes only deleted Euler factors,
not principality of the cubic numerator character. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicNumeratorChar_mul_cube_ne_one (hpub : CubicSupplementaryPeriodicity)
    {r c : Eisenstein} (hr : r ≠ 0) (hc : c ≠ 0)
    (hn : cubicNumeratorChar hpub r hr ≠ 1) :
    cubicNumeratorChar hpub (r*c^3) (mul_ne_zero hr (pow_ne_zero _ hc)) ≠ 1 := by
  obtain ⟨x,hx,hcop,hne⟩ := (cubicNumeratorChar_ne_one_iff hpub r hr).mp hn
  obtain ⟨y,hy,hcy⟩ := exists_coprime_residue_lift hc hcop
  have hyx : (3:Eisenstein) ∣ y-x :=
    (show (3:Eisenstein) ∣ 9*r from ⟨3*r,by ring⟩).trans hy
  have hyp : primary y := by
    change (3:Eisenstein) ∣ y-1
    convert dvd_add hyx hx using 1
    ring
  have hyc : IsCoprime y c := hcy.of_mul_left_right.symm
  have hyr : IsCoprime r y := hcy.of_mul_left_left.of_mul_left_right
  have hy9 : IsCoprime (9:Eisenstein) y := hcy.of_mul_left_left.of_mul_left_left
  apply (cubicNumeratorChar_ne_one_iff hpub (r*c^3) (mul_ne_zero hr (pow_ne_zero _ hc))).mpr
  refine ⟨y,hyp,hy9.mul_left (hyr.mul_left (hyc.symm.pow_left (m := 3))),?_⟩
  rw [cubicSymbol_mul_upper hyp,cubicSymbol_pow_upper hyp,
    cubicSymbol_cube_of_isCoprime hyp c hyc,mul_one,hpub r hr y x hyp hx hy]
  exact hne

lemma cubicNumeratorChar_mul_cube_ne_one_iff (hpub : CubicSupplementaryPeriodicity)
    {r c : Eisenstein} (hr : r ≠ 0) (hc : c ≠ 0) :
    cubicNumeratorChar hpub (r*c^3) (mul_ne_zero hr (pow_ne_zero _ hc)) ≠ 1 ↔
      cubicNumeratorChar hpub r hr ≠ 1 := by
  constructor
  · intro hn
    obtain ⟨x,hx,hcop,hne⟩ :=
      (cubicNumeratorChar_ne_one_iff hpub (r*c^3) (mul_ne_zero hr (pow_ne_zero _ hc))).mp hn
    have hxr : IsCoprime r x := hcop.of_mul_left_right.of_mul_left_left
    have hxc : IsCoprime x c :=
      (hcop.of_mul_left_right.of_mul_left_right).of_isCoprime_of_dvd_left (dvd_pow_self c (by norm_num : 3 ≠ 0)) |>.symm
    have hx9 : IsCoprime (9:Eisenstein) x := hcop.of_mul_left_left
    apply (cubicNumeratorChar_ne_one_iff hpub r hr).mpr
    refine ⟨x,hx,hx9.mul_left hxr,?_⟩
    simpa only [cubicSymbol_mul_upper hx,cubicSymbol_pow_upper hx,
      cubicSymbol_cube_of_isCoprime hx c hxc,mul_one] using hne
  · exact cubicNumeratorChar_mul_cube_ne_one hpub hr hc

end CubicFirstMoment

end

end OAI
