module

public import ArtinMatthews.IdealCharacterCellApply
public import ArtinMatthews.IdealConditionalCharacterActual


set_option backward.privateInPublic true
@[expose] public section

/-! The full, literal Source03 log-cell kernel has norm at most two
on the original harmonic product space. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem idealCharacterCellApply_actual (a c d X v₀ : ℝ)
    (ha : 0 ≤ a) (hc : 0 < c) (hd : 0 ≤ d) (hX : 0 ≤ X) (hv₀ : 0 < v₀) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (Q : ℕ), (Q : ℝ) ≤ L^a →
        ∀ (P : I → Finset ℕ), (∀ i p, p ∈ P i → p.Prime) →
        (∀ i, 0 < bandReciprocalMass (P i)) →
        (∀ i p, p ∈ P i → Real.exp (L^c) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (L^d)) →
        ∀ i : I, IdealPrimeInterval (P i) → v₀ ≤ bandReciprocalMass (P i) →
        ∀ (h : ℝ), 0 < h → ∀ f : IdealSelectedLabels P → ℂ,
          idealFrameEnergy (idealSelectedMass P) (idealCharacterCellApply P Q h (L^(-X)) f) ≤
            4 * idealFrameEnergy (idealSelectedMass P) f := by
  filter_upwards [idealConditionalCharacterFrame_actual (I := I) a c d X v₀ ha hc hd hX hv₀,
    eventually_gt_atTop (0 : ℝ)] with L hframe hL
  intro Q hQ P hP hV hbounds i hinterval hVlo h hh f
  apply idealCharacterCellApply_energy_le P hV Q h (Real.rpow_pos_of_pos hL _) (by norm_num)
  intro j hj g
  exact hframe Q hQ P hP hV hbounds i hinterval hVlo h hh j hj g

end
end ArtinMatthews
