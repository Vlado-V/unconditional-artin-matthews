module

public import ArtinMatthews.MarkedTypeIIDyadReassembly
public import ArtinMatthews.GiantMarkedSelectedDamping


set_option backward.privateInPublic true
@[expose] public section

/-! The smooth dyad sum is exactly the same literal replaced source used
in the selected-squareful damping estimate. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators
noncomputable section

theorem markedTypeII_reassembled_damping_eq_quotientDampedSum {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (M N : Finset ℕ) (α β F : ℕ → ℂ) :
    (∑ a∈markedMajorLabelSet P,∑ m∈M,∑ n∈N,if a∣m*n-1 then
      markedTypeIIQuotientDampedCore P F ((m*n-1)/a)*(markedMajorLabelMass P:ℂ)*α m*β n else 0)=
    giantMarkedQuotientDampedSum P M N α β F := by
  unfold giantMarkedQuotientDampedSum
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  split_ifs
  · unfold markedTypeIIQuotientDampedCore
    ring
  · rfl

theorem markedTypeII_actual_label_dyad_reassembly_eq_quotientDampedSum {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ)≤e j) (heUpper : ∀ j,e j≤(1/5:ℝ))
    (hgroups : 2≤Fintype.card J) :
    ∀ᶠ x : ℝ in atTop,∀ (M N : Finset ℕ) (α β F : ℕ → ℂ),
      let P := fun j => markedLogPowerBand (e j) x
      (∑ j∈markedTypeIILabelDyadIndices (markedMajorLabelSet P),
        markedTypeIISelectedLabelDyadSum P ((2:ℝ)^j) M N α β F) =
      giantMarkedQuotientDampedSum P M N α β F := by
  filter_upwards [markedTypeII_actual_label_dyad_reassembly e he heUpper hgroups] with x hx
  intro M N α β F
  exact (hx M N α β F).trans (markedTypeII_reassembled_damping_eq_quotientDampedSum _ M N α β F)

end
end ArtinMatthews
