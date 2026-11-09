module

public import ArtinMatthews.MarkedMajorArcHeight
public import OAI.NumberTheory.TwoPoint.Halasz.HalaszWeakHurwitzTheorem
public import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWeakVKStrip


set_option backward.privateInPublic true
@[expose] public section

/-! An unconditional character rectangle from the actual Vinogradov-system
and Hurwitz growth proofs. No zero-free or prime-cancellation input is
assumed in the result below. -/
namespace ArtinMatthews

open Filter OAI.TwoPointCorrelations
open scoped Topology

/-- Uniform genuine zero-freeness and logarithmic-derivative control at the
full polynomial frequency range needed before the long-prime Mellin shift.
The lower height cutoff excludes the possible pole at one. -/
theorem marked_major_arc_character_rectangle (A b : ℝ)
    (hA : 0 ≤ A) (hb : 0 ≤ b) :
    ∃ K T : ℝ, 0 < K ∧ 0 < T ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q], (q:ℝ) ≤ L^A →
      ∀ (χ : DirichletCharacter ℂ q) (s : ℂ),
      T ≤ |s.im| → |s.im| ≤ Real.exp (b*L) →
      1-L^(-(3/4:ℝ)) ≤ s.re → s.re ≤ 1+1/L →
      DirichletCharacter.LFunction χ s ≠ 0 ∧
      ‖deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s‖ ≤ K*L^2 := by
  obtain ⟨c,K,T,hc,hK,hT,hstrip⟩ := mrt_weak_hurwitz_growth.strip_logderiv
  refine ⟨K,T,hK,hT,?_⟩
  filter_upwards [marked_major_arc_character_budget A b c hA hb hc]
    with L hbudget
  intro q _ hq χ s hTlo hThi hσlo hσhi
  have hpar := hbudget q hq s.im hThi
  have hsrep : (s.re:ℂ)+Complex.I*(s.im:ℂ) = s := by
    rw [mul_comm]
    exact Complex.re_add_im s
  have hh := hstrip q χ s.im s.re hTlo (by linarith [hpar.1])
    (by linarith [hpar.2.2])
  rw [hsrep] at hh
  exact ⟨hh.1, hh.2.trans (by simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left hpar.2.1 hK.le))⟩

end ArtinMatthews
