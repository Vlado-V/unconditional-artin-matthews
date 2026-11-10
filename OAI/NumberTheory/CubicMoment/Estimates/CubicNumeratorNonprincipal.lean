module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.NumberTheory.MulChar.Lemmas
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
public import OAI.NumberTheory.CubicGram.Reciprocity
public import OAI.NumberTheory.CubicMoment.Estimates.CubicNumeratorOrder
public import OAI.NumberTheory.CubicMoment.Estimates.MixedCharacterSieve
public import OAI.NumberTheory.CubicMoment.Estimates.PrimaryCharacterNonprincipal


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-! Nontrivial cubic numerator characters in the squarefree primary case,
using the mixed-character Fourier witness and reciprocity. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicNumeratorChar_squarefree_nonprincipal (hpub : CubicSupplementaryPeriodicity)
    {v : Eisenstein} (hv : primary v) (hvs : Squarefree v) (hvu : ¬ IsUnit v) :
    cubicNumeratorChar hpub v (primary_ne_zero hv) ≠ 1 := by
  have hnu : ¬ IsUnit (v*1) := by simpa only [mul_one] using hvu
  obtain ⟨x,hx,hcop,hne⟩ := mixedCubic_nonprincipal hv primary_one hvs
    squarefree_one isCoprime_one_right hnu
  have hcopv : IsCoprime v x := by simpa only [mul_one] using hcop
  have hcop9 : IsCoprime (9:Eisenstein) x := by
    convert ((primary_coprime_three hx).symm.pow_left (m := 2)) using 1
    norm_num
  apply (cubicNumeratorChar_ne_one_iff hpub v (primary_ne_zero hv)).mpr
  refine ⟨x,hx,hcop9.mul_left hcopv,?_⟩
  have hne' : cubicSymbol v x ≠ 1 := by
    simpa only [mixedCubic,cubicSymbol_one_lower,star_one,mul_one] using hne
  rwa [cubic_reciprocity hx hv]

lemma cubicNumeratorChar_squarefree_nonreal (hpub : CubicSupplementaryPeriodicity)
    {v : Eisenstein} (hv : primary v) (hvs : Squarefree v) (hvu : ¬ IsUnit v) :
    star (cubicNumeratorChar hpub v (primary_ne_zero hv)) ≠
      cubicNumeratorChar hpub v (primary_ne_zero hv) :=
  cubicNumeratorChar_not_self_conjugate hpub v (primary_ne_zero hv)
    (cubicNumeratorChar_squarefree_nonprincipal hpub hv hvs hvu)

end CubicFirstMoment

end

end OAI
