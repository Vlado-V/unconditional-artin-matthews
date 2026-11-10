module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.DirichletL.CubicSieve.ChildTransfer
public import OAI.NumberTheory.DirichletL.Descent.Marks
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
public import OAI.NumberTheory.DirichletL.Inversion.InitialArithmetic


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialInputReindex
open ActualEisensteinCubic FirstCauchyArithmetic SecondPassArithmetic InverseMoment
open InverseInitialArithmetic
local notation "O"=>ActualEisensteinCubic.O

theorem input_puncture_span {ι:Type*}[DecidableEq ι](p:ι→O)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(Ψ:O→*ℂ)(j₁ j₂:O)(hspan:Ideal.span {j₁}=Ideal.span {j₂})
    (test:Finset ι→ℂ)(u:O):
    inputConjugateRow p hg pool Ψ j₁ 1 1 test u=
      inputConjugateRow p hg pool Ψ j₂ 1 1 test u:=by
  rw [initial_input_row p hg,initial_input_row p hg]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro A hA
  dsimp only
  rw [rowCoprimeMask_eq_of_span_eq (fun i=>Ideal.span {p i}) A hspan]

theorem primeMark_subtype {σ ι:Type*}[DecidableEq σ][DecidableEq ι]
    (I:Finset σ)(L:σ→Finset ι)(a:σ→ι→ℂ)(A:Finset ι):
    primeMark Finset.univ (fun i:I=>L i.val) (fun i:I=>a i.val) A=
      primeMark I L a A:=by
  exact Finset.prod_coe_sort I (fun i=>primeSlot (L i) (a i) A)

theorem primeMark_remaining {σ ι:Type*}[Fintype σ][DecidableEq σ][DecidableEq ι]
    (J:Finset σ)(L:σ→Finset ι)(a:σ→ι→ℂ)(A:Finset ι):
    primeMark Finset.univ (fun i:{i:σ//i∉J}=>L i.val) (fun i:{i:σ//i∉J}=>a i.val) A=
      primeMark (Finset.univ\J) L a A:=by
  classical
  unfold primeMark
  exact (Finset.prod_subtype (Finset.univ\J) (by intro i;simp)
    (fun i=>primeSlot (L i) (a i) A)).symm

end SevenEighths.InverseInitialInputReindex

end

end OAI
