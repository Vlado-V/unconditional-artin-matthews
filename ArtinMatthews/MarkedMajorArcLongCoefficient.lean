module

public import ArtinMatthews.MarkedMajorArcHighCentered
public import ArtinMatthews.MarkedMajorArcLowCentered
public import ArtinMatthews.MarkedMajorArcConjugate


set_option backward.privateInPublic true
@[expose] public section

/-! The complete major-arc long-coefficient estimate: all frequencies in
the original exponential-times-polynomial range, with actual prime/rough
centering, every character, modulation, and arbitrary dyadic subinterval. -/
namespace ArtinMatthews
open Filter
open scoped Topology

 theorem marked_major_long_coefficient (a η τ C b K P : ℝ)
    (ha : 0 ≤ a) (hη : 0 < η) (hτ : 0 < τ) (hC : 0 ≤ C) (hP : 0 ≤ P) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (modulation t H u v : ℝ),
        (q:ℝ) ≤ L^a → |modulation| ≤ L^C → |t| ≤ K*Real.exp L*L^b →
        Real.exp (τ*L) ≤ H → H ≤ u → u ≤ v → v ≤ 2*H → v ≤ Real.exp (η*L) →
        ‖markedMajorCenteredSum χ (Real.exp (L^(6/25:ℝ))) modulation t H u v‖ ≤ L^(-P) := by
  obtain ⟨T,hT,hhigh⟩ := marked_major_high_centered_cancellation a η τ C b K P ha hη hτ hP
  filter_upwards [hhigh,marked_major_low_centered_cancellation a η τ C T P ha hη hτ hC hT.le hP]
    with L hhigh hlow
  intro q _ χ modulation t H u v hq hm ht hH hHu huv hvH hvhi
  by_cases hlo : L^T ≤ |t|
  · exact hhigh q χ modulation t H u v hq hm hlo ht hH hHu huv hvH hvhi
  · exact hlow q χ modulation t H u v hq hm (le_of_not_ge hlo) hH hHu huv hvH hvhi

/-- The same quantitative estimate for the literal conjugated coefficients.
Characters are arbitrary in both conclusions, so this also includes their
conjugates. -/
theorem marked_major_long_coefficient_and_conjugate (a η τ C b K P : ℝ)
    (ha : 0 ≤ a) (hη : 0 < η) (hτ : 0 < τ) (hC : 0 ≤ C) (hP : 0 ≤ P) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (modulation t H u v : ℝ),
        (q:ℝ) ≤ L^a → |modulation| ≤ L^C → |t| ≤ K*Real.exp L*L^b →
        Real.exp (τ*L) ≤ H → H ≤ u → u ≤ v → v ≤ 2*H → v ≤ Real.exp (η*L) →
        ‖markedMajorCenteredSum χ (Real.exp (L^(6/25:ℝ))) modulation t H u v‖ ≤ L^(-P) ∧
        ‖markedMajorConjugateCenteredSum χ (Real.exp (L^(6/25:ℝ))) modulation t H u v‖ ≤ L^(-P) := by
  filter_upwards [marked_major_long_coefficient a η τ C b K P ha hη hτ hC hP]
    with L hL
  intro q _ χ modulation t H u v hq hm ht hH hHu huv hvH hvhi
  refine ⟨hL q χ modulation t H u v hq hm ht hH hHu huv hvH hvhi,?_⟩
  rw [marked_conjugate_centered_sum_eq]
  exact hL q χ (-modulation) t H u v hq (by simpa only [abs_neg] using hm)
    ht hH hHu huv hvH hvhi

end ArtinMatthews
