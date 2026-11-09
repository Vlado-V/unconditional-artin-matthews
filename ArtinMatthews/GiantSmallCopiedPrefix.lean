module

public import ArtinMatthews.GiantSmallConditioningJoint


set_option backward.privateInPublic true
@[expose] public section

/-! Two full small marking lists with a common copied prefix have an
exact ordered-prefix and independent-tail parametrization. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} {P : J → Finset ℕ} {k ell : ℕ}

def giantSmallPrefix (a : MarkedPhysicalMarking P (k+ell)) :
    MarkedPhysicalMarking P k := fun j i => a j (Fin.castAdd ell i)

theorem giantSmallPrefix_append (d : MarkedPhysicalMarking P k)
    (r : MarkedPhysicalMarking P ell) :
    giantSmallPrefix (giantSmallAppend d r) = d := by
  funext j i
  exact Fin.append_left _ _ i

variable [Fintype J] [DecidableEq J]

theorem giantSmallCopiedTarget_sum (a : MarkedPhysicalMarking P (k+ell))
    (F : MarkedPhysicalMarking P (k+ell) → ℂ) :
    (∑ b : MarkedPhysicalMarking P (k+ell),
      if giantSmallPrefix b = giantSmallPrefix a then F b else 0) =
        ∑ r : MarkedPhysicalMarking P ell, F (giantSmallAppend (giantSmallPrefix a) r) := by
  rw [← giantSmallAppend_sum (f := fun b =>
    if giantSmallPrefix b = giantSmallPrefix a then F b else 0)]
  simp only [giantSmallPrefix_append]
  rw [Finset.sum_eq_single (giantSmallPrefix a)]
  · simp
  · intro d _ hd
    simp only [hd, ite_false, Finset.sum_const_zero]
  · intro h
    exact (h (Finset.mem_univ _)).elim

theorem giantSmallCopiedPair_sum
    (F : MarkedPhysicalMarking P (k+ell) → MarkedPhysicalMarking P (k+ell) → ℂ) :
    (∑ a : MarkedPhysicalMarking P (k+ell), ∑ b : MarkedPhysicalMarking P (k+ell),
      if giantSmallPrefix b = giantSmallPrefix a then F a b else 0) =
      ∑ d : MarkedPhysicalMarking P k, ∑ r : MarkedPhysicalMarking P ell,
        ∑ r' : MarkedPhysicalMarking P ell, F (giantSmallAppend d r) (giantSmallAppend d r') := by
  simp_rw [giantSmallCopiedTarget_sum]
  rw [← giantSmallAppend_sum (f := fun a =>
    ∑ r' : MarkedPhysicalMarking P ell, F a (giantSmallAppend (giantSmallPrefix a) r'))]
  simp only [giantSmallPrefix_append]

end
end ArtinMatthews
