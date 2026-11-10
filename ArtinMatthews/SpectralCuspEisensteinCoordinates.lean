module

public import ArtinMatthews.SpectralCuspEisensteinResidueRows
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.Order.Interval.Finset.Box
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

/-! Exact positive-row coordinates for every pair of actual cusps. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace ArtinMatthews

abbrev CuspEisensteinPositiveCoordinates (N : ℕ) (r a : SL(2,ℤ)) :=
  Σ c : {c : ℕ // 0 < c}, CuspEisensteinRowFibre N r a c.val

def cuspEisensteinPositiveCoordinateRow (N : ℕ) (r a : SL(2,ℤ))
    (v : CuspEisensteinPositiveCoordinates N r a) : CuspEisensteinPositiveRows N r a :=
  ⟨⟨![(v.1.val:ℤ),v.2.val],v.2.property⟩,by
    change 0 < (v.1.val:ℤ)
    exact_mod_cast v.1.property⟩

def cuspEisensteinPositiveRowCoordinate (N : ℕ) (r a : SL(2,ℤ))
    (v : CuspEisensteinPositiveRows N r a) : CuspEisensteinPositiveCoordinates N r a := by
  have hv : ((v.val.val 0).toNat:ℤ)=v.val.val 0 := Int.toNat_of_nonneg v.property.le
  refine ⟨⟨(v.val.val 0).toNat,by omega⟩,⟨v.val.val 1,?_⟩⟩
  have he : ![(((v.val.val 0).toNat):ℤ),v.val.val 1]=v.val.val := by
    funext i
    fin_cases i
    · exact hv
    · rfl
  rw [he]
  exact v.val.property

def cuspEisensteinPositiveCoordinateEquiv (N : ℕ) (r a : SL(2,ℤ)) :
    CuspEisensteinPositiveCoordinates N r a ≃ CuspEisensteinPositiveRows N r a where
  toFun := cuspEisensteinPositiveCoordinateRow N r a
  invFun := cuspEisensteinPositiveRowCoordinate N r a
  left_inv v := by
    rcases v with ⟨⟨c,hc⟩,⟨d,hd⟩⟩
    simp [cuspEisensteinPositiveRowCoordinate,cuspEisensteinPositiveCoordinateRow]
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    fin_cases i
    · simp [cuspEisensteinPositiveRowCoordinate,cuspEisensteinPositiveCoordinateRow,
        Int.toNat_of_nonneg v.property.le]
    · rfl

end ArtinMatthews
