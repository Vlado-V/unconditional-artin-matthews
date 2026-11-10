module

public import Mathlib.Algebra.Group.End
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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


set_option backward.privateInPublic true
@[expose] public section

/-! Mapping a list by an equivalence preserves its exact index order.
The statement permits arbitrary proof transports of the index lengths. -/
namespace ArtinMatthews

variable {A B : Type*} (e : A ≃ B)

theorem markedMemoryRelabel_list_get (l : List A) (l' : List B) (h : l' = l.map e)
    (i : Fin l'.length) (j : Fin l.length) (hij : i.val = j.val) :
    e.symm (l'.get i) = l.get j := by
  subst l'
  simp only [List.get_eq_getElem, List.getElem_map, Equiv.symm_apply_apply, hij]

theorem markedMemoryRelabel_list_get_forward (l : List A) (l' : List B) (h : l' = l.map e)
    (i : Fin l'.length) (j : Fin l.length) (hij : i.val = j.val) :
    l'.get i = e (l.get j) :=
  e.symm_apply_eq.mp (markedMemoryRelabel_list_get e l l' h i j hij)

end ArtinMatthews
