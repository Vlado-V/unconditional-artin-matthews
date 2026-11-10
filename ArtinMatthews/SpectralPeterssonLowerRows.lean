module

public import ArtinMatthews.SpectralPeterssonCuspRows
public import ArtinMatthews.SpectralTrueWidthDoubleCosets
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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


set_option backward.privateInPublic true
@[expose] public section

/-! Actual nonzero lower rows are the true-width reduced double cosets
with one remaining right integer translation. -/

noncomputable section
open Matrix
open scoped MatrixGroups

namespace ArtinMatthews

def Gamma0PeterssonLowerRow (N : ℕ) (b a : SL(2, ℤ)) (c : ℕ) :=
  {p : Gamma0PeterssonSignedRow N b a // p.val 0 = (c : ℤ)}

def gamma0PeterssonLowerRowExpand (N : ℕ) [NeZero N] (b a : SL(2, ℤ)) (c : ℕ)
    (p : gamma0TrueWidthReducedMatrix N b a c × ℤ) : Gamma0PeterssonLowerRow N b a c :=
  let M := gamma0TrueWidthDoubleCosetExpand N b a c (p.1,0,p.2)
  ⟨gamma0PeterssonRowOfMatrix N b a ⟨M.val,M.property.1⟩, M.property.2⟩

private theorem gamma0Petersson_expanded_bottomRow (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (c : ℕ) (R : gamma0TrueWidthReducedMatrix N b a c) (l k : ℤ) :
    (fun i => (gamma0TrueWidthDoubleCosetExpand N b a c (R,l,k)).val 1 i) =
      fun i => (R.val*integerTranslation ((gamma0CuspTrueWidth N b : ℤ)*k)) 1 i := by
  change (fun i => (integerTranslation ((gamma0CuspTrueWidth N a : ℤ)*l)*R.val*
    integerTranslation ((gamma0CuspTrueWidth N b : ℤ)*k)) 1 i) = _
  rw [mul_assoc]
  funext i
  let A := integerTranslation ((gamma0CuspTrueWidth N a : ℤ)*l)
  let M := R.val*integerTranslation ((gamma0CuspTrueWidth N b : ℤ)*k)
  change (A.val*M.val) 1 i = M.val 1 i
  simp [A,Matrix.mul_apply,Fin.sum_univ_two,integerTranslation]

theorem gamma0PeterssonLowerRowExpand_bijective (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (c : ℕ) [NeZero c] : Function.Bijective (gamma0PeterssonLowerRowExpand N b a c) := by
  constructor
  · rintro ⟨R,k⟩ ⟨R',k'⟩ he
    let M := gamma0TrueWidthDoubleCosetExpand N b a c (R,0,k)
    let M' := gamma0TrueWidthDoubleCosetExpand N b a c (R',0,k')
    have hrow := congrArg (fun p : Gamma0PeterssonLowerRow N b a c => p.val.val) he
    change (fun i => M.val 1 i) = (fun i => M'.val 1 i) at hrow
    obtain ⟨l,hl⟩ := gamma0Petersson_left_translate_of_row_eq N b a
      ⟨M.val,M.property.1⟩ ⟨M'.val,M'.property.1⟩
      (congrFun hrow.symm 0) (congrFun hrow.symm 1)
    have hm : M.val = R.val*integerTranslation ((gamma0CuspTrueWidth N b : ℤ)*k) := by
      simp only [M,gamma0TrueWidthDoubleCosetExpand,mul_zero,integerTranslation_eq_T_zpow,zpow_zero,one_mul]
    have hh : gamma0TrueWidthDoubleCosetExpand N b a c (R',0,k') =
        gamma0TrueWidthDoubleCosetExpand N b a c (R,l,k) := by
      apply Subtype.ext
      change M'.val = _
      change M'.val = integerTranslation ((gamma0CuspTrueWidth N a : ℤ)*l)*M.val at hl
      rw [hl,hm]
      exact (mul_assoc _ _ _).symm
    have h := gamma0TrueWidthDoubleCosetExpand_injective N b a c hh
    exact Prod.ext (congrArg Prod.fst h).symm (congrArg (fun p => p.2.2) h).symm
  · intro p
    let M := gamma0PeterssonRowMatrix N b a p.val
    have hM := gamma0PeterssonRowMatrix_row N b a p.val
    let F : gamma0CuspMatrixFibre N b a c :=
      ⟨M.val,M.property,(congrFun hM 0).trans p.property⟩
    obtain ⟨⟨R,l,k⟩,he⟩ := gamma0TrueWidthDoubleCosetExpand_surjective N b a c F
    refine ⟨(R,k), Subtype.ext (Subtype.ext ?_)⟩
    change (fun i => (gamma0TrueWidthDoubleCosetExpand N b a c (R,0,k)).val 1 i) = p.val.val
    calc
      _ = (fun i => (R.val*integerTranslation ((gamma0CuspTrueWidth N b : ℤ)*k)) 1 i) :=
        gamma0Petersson_expanded_bottomRow N b a c R 0 k
      _ = (fun i => (gamma0TrueWidthDoubleCosetExpand N b a c (R,l,k)).val 1 i) :=
        (gamma0Petersson_expanded_bottomRow N b a c R l k).symm
      _ = p.val.val := (congrArg (fun M : gamma0CuspMatrixFibre N b a c => fun i => M.val 1 i) he).trans hM

def gamma0PeterssonLowerRowEquiv (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (c : ℕ) [NeZero c] : (gamma0TrueWidthReducedMatrix N b a c × ℤ) ≃
      Gamma0PeterssonLowerRow N b a c :=
  Equiv.ofBijective _ (gamma0PeterssonLowerRowExpand_bijective N b a c)

end ArtinMatthews
