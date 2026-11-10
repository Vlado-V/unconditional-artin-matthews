module

public import ArtinMatthews.SpectralCuspEisensteinSeries
public import ArtinMatthews.SpectralCuspEisensteinResidueRows
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Exact sign accounting for the genuine all-cusp row family. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace ArtinMatthews

abbrev CuspEisensteinZeroRows (N : ℕ) (r a : SL(2,ℤ)) :=
  {v : Gamma0CuspEisensteinRows N r a // v.val 0=0}

abbrev CuspEisensteinSignedIndex (N : ℕ) (r a : SL(2,ℤ)) :=
  CuspEisensteinZeroRows N r a ⊕ (CuspEisensteinPositiveRows N r a × Bool)

def cuspEisensteinSignedRow (N : ℕ) (r a : SL(2,ℤ)) :
    CuspEisensteinSignedIndex N r a → Gamma0CuspEisensteinRows N r a
  | .inl v => v.val
  | .inr (v,b) => if b then v.val else gamma0CuspEisensteinNegRow N r a v.val

def cuspEisensteinSignedRowInverse (N : ℕ) (r a : SL(2,ℤ))
    (v : Gamma0CuspEisensteinRows N r a) : CuspEisensteinSignedIndex N r a :=
  if h0 : v.val 0=0 then .inl ⟨v,h0⟩
  else if hp : 0 < v.val 0 then .inr (⟨v,hp⟩,true)
  else .inr (⟨gamma0CuspEisensteinNegRow N r a v,by change 0 < -v.val 0; omega⟩,false)

def cuspEisensteinSignedRowEquiv (N : ℕ) (r a : SL(2,ℤ)) :
    CuspEisensteinSignedIndex N r a ≃ Gamma0CuspEisensteinRows N r a where
  toFun := cuspEisensteinSignedRow N r a
  invFun := cuspEisensteinSignedRowInverse N r a
  left_inv i := by
    rcases i with v | ⟨v,b⟩
    · simp [cuspEisensteinSignedRow,cuspEisensteinSignedRowInverse,v.property]
    · cases b
      · simp [cuspEisensteinSignedRow,cuspEisensteinSignedRowInverse,
          gamma0CuspEisensteinNegRow,v.property.ne',v.property.le]
      · simp [cuspEisensteinSignedRow,cuspEisensteinSignedRowInverse,v.property.ne',v.property]
  right_inv v := by
    by_cases h0 : v.val 0=0
    · simp [cuspEisensteinSignedRowInverse,h0,cuspEisensteinSignedRow]
    · by_cases hp : 0 < v.val 0
      · simp [cuspEisensteinSignedRowInverse,h0,hp,cuspEisensteinSignedRow]
      · simp [cuspEisensteinSignedRowInverse,h0,hp,cuspEisensteinSignedRow]

theorem cuspEisenstein_signed_tsum (N : ℕ) (r a : SL(2,ℤ))
    (f : Gamma0CuspEisensteinRows N r a → ℂ) (hf : Summable f)
    (hneg : ∀ v, f (gamma0CuspEisensteinNegRow N r a v)=f v) :
    (∑' v, f v) = (∑' v : CuspEisensteinZeroRows N r a, f v.val)+
      2*(∑' v : CuspEisensteinPositiveRows N r a, f v.val) := by
  let e := cuspEisensteinSignedRowEquiv N r a
  have hg : Summable (fun i => f (e i)) := e.summable_iff.mpr hf
  have hL : Summable (fun v : CuspEisensteinZeroRows N r a => f (e (.inl v))) :=
    hg.comp_injective (i := Sum.inl) Sum.inl_injective
  have hR : Summable (fun p : CuspEisensteinPositiveRows N r a × Bool => f (e (.inr p))) :=
    hg.comp_injective (i := Sum.inr) Sum.inr_injective
  have hsplit := Summable.tsum_sum (f := fun i : CuspEisensteinSignedIndex N r a => f (e i)) hL hR
  have hprod := Summable.tsum_prod
    (f := fun p : CuspEisensteinPositiveRows N r a × Bool => f (e (.inr p))) hR
  rw [← e.tsum_eq f,hsplit,hprod]
  simp [e,cuspEisensteinSignedRowEquiv,cuspEisensteinSignedRow,hneg,← two_mul,tsum_mul_left]

theorem cuspEisensteinRowTerm_neg (N : ℕ) (r a : SL(2,ℤ)) (s : ℂ)
    (v : Gamma0CuspEisensteinRows N r a) (z : UpperHalfPlane) :
    cuspEisensteinRowTerm N r a s (gamma0CuspEisensteinNegRow N r a v) z =
      cuspEisensteinRowTerm N r a s v z := by
  simp only [cuspEisensteinRowTerm,cuspEisensteinRowHeight_row,
    gamma0CuspEisensteinNegRow,Pi.neg_apply,Int.cast_neg,neg_mul,← neg_add,norm_neg]

theorem cuspEisensteinZeroRows_unit (N : ℕ) (r a : SL(2,ℤ))
    (v : CuspEisensteinZeroRows N r a) : v.val.val 1=1 ∨ v.val.val 1= -1 := by
  have h := gamma0CuspEisensteinRows_coprime N r a v.val
  rw [v.property,isCoprime_zero_left] at h
  exact Int.isUnit_iff.mp h

theorem cuspEisensteinRowTerm_zero (N : ℕ) (r a : SL(2,ℤ)) (s : ℂ)
    (v : CuspEisensteinZeroRows N r a) (z : UpperHalfPlane) :
    cuspEisensteinRowTerm N r a s v.val z = (z.im:ℂ)^s := by
  rcases cuspEisensteinZeroRows_unit N r a v with h | h <;>
    simp [cuspEisensteinRowTerm,cuspEisensteinRowHeight_row,v.property,h]

end ArtinMatthews
