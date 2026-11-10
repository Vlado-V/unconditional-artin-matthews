module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Nat.Totient
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! The canonical generator generates its actual simple intermediate field. -/

namespace ArtinMatthews

theorem adjoinSimple_gen_adjoin_eq_top
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    {α : L} (hα : IsIntegral F α) :
    IntermediateField.adjoin F {IntermediateField.AdjoinSimple.gen F α} = ⊤ := by
  let : FiniteDimensional F (IntermediateField.adjoin F {α}) :=
    IntermediateField.adjoin.finiteDimensional hα
  apply IntermediateField.adjoin_eq_top_iff.mpr
  simpa only [IntermediateField.adjoin.powerBasis_gen] using
    (IntermediateField.adjoin.powerBasis hα).adjoin_gen_eq_top

end ArtinMatthews
