module

public import ArtinMatthews.IdealCellPhaseComparison
public import ArtinMatthews.IdealLogCellPartition
public import ArtinMatthews.IdealKernelGoodBad


set_option backward.privateInPublic true
@[expose] public section

/-! The actual phase comparison on retained logarithmic cells extends
to arbitrary full-tuple tests with the exact discarded-cell masses. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

theorem idealFullCellPhaseAverage_discarded (P : A → Finset ℕ) (R : B → Finset ℕ)
    (Q : ℕ) (h ξ ζ α : ℝ) (x : IdealSelectedLabels P) (y : IdealSelectedLabels R)
    (hbad : idealLogCellMass P h (idealLogCell h x) < ξ ∨
      idealLogCellMass R h (idealLogCell h y) < ξ) :
    idealFullCellPhaseAverage P R Q h ξ ζ α x y = 0 := by
  unfold idealFullCellPhaseAverage
  apply sum_eq_zero
  intro d _
  apply sum_eq_zero
  intro e _
  rcases hbad with hx | hy
  · rw [idealCharacterCellKernel_discarded P Q h ξ d x hx]
    ring
  · rw [idealCharacterCellKernel_discarded R Q h ξ e y hy]
    ring

theorem idealProductPhase_norm (ζ α : ℝ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    ‖idealProductPhase ζ α n m‖ = 1 := by
  rw [← idealLogPhase_product ζ α hn hm]
  exact idealLogPhase_norm _ _ _

theorem idealCellPhaseBilinear_sq_le
    (P : A → Finset ℕ) (R : B → Finset ℕ)
    (hP : ∀ i p, p ∈ P i → p.Prime) (hR : ∀ i p, p ∈ R i → p.Prime)
    (hVP : ∀ i, 0 < bandReciprocalMass (P i)) (hVR : ∀ i, 0 < bandReciprocalMass (R i))
    (Q : ℕ) (h ξ ζ α : ℝ) (f : IdealSelectedLabels P → ℂ) (g : IdealSelectedLabels R → ℂ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hretained : ∀ x y, f x ≠ 0 → g y ≠ 0 →
      ξ ≤ idealLogCellMass P h (idealLogCell h x) →
      ξ ≤ idealLogCellMass R h (idealLogCell h y) →
      ‖idealProductPhase ζ α (idealSelectedProduct x) (idealSelectedProduct y) -
        idealFullCellPhaseAverage P R Q h ξ ζ α x y‖ ≤ ε) :
    ‖∑ x : IdealSelectedLabels P, (idealSelectedMass P x : ℂ)*f x*
      ∑ y : IdealSelectedLabels R, (idealSelectedMass R y : ℂ)*g y*
        (idealProductPhase ζ α (idealSelectedProduct x) (idealSelectedProduct y) -
          idealFullCellPhaseAverage P R Q h ξ ζ α x y)‖^2 ≤
      (ε^2+idealDiscardedCellMass P h ξ+idealDiscardedCellMass R h ξ)*
        idealFrameEnergy (idealSelectedMass P) f*idealFrameEnergy (idealSelectedMass R) g := by
  let goodP (x : IdealSelectedLabels P) := ξ ≤ idealLogCellMass P h (idealLogCell h x)
  let goodR (y : IdealSelectedLabels R) := ξ ≤ idealLogCellMass R h (idealLogCell h y)
  let E (x : IdealSelectedLabels P) (y : IdealSelectedLabels R) :=
    idealProductPhase ζ α (idealSelectedProduct x) (idealSelectedProduct y) -
      idealFullCellPhaseAverage P R Q h ξ ζ α x y
  let K (x : IdealSelectedLabels P) (y : IdealSelectedLabels R) :=
    if f x = 0 ∨ g y = 0 then 0 else E x y
  have hk (x : IdealSelectedLabels P) (y : IdealSelectedLabels R)
      (hx : goodP x) (hy : goodR y) : ‖K x y‖ ≤ ε := by
    by_cases hz : f x = 0 ∨ g y = 0
    · simpa only [K, ite_eq_left hz, norm_zero] using hε
    · rw [show K x y = E x y from ite_eq_right hz]
      exact hretained x y (fun he => hz (Or.inl he)) (fun he => hz (Or.inr he)) hx hy
  have hbad (x : IdealSelectedLabels P) (y : IdealSelectedLabels R)
      (hxy : ¬(goodP x ∧ goodR y)) : ‖K x y‖ ≤ 1 := by
    by_cases hz : f x = 0 ∨ g y = 0
    · simp only [K, ite_eq_left hz, norm_zero, zero_le_one]
    · have hdiscard : idealLogCellMass P h (idealLogCell h x) < ξ ∨
          idealLogCellMass R h (idealLogCell h y) < ξ := by
        by_cases hx : goodP x
        · exact Or.inr (lt_of_not_ge (fun hy => hxy ⟨hx, hy⟩))
        · exact Or.inl (lt_of_not_ge hx)
      rw [show K x y = E x y from ite_eq_right hz]
      dsimp only [E]
      rw [idealFullCellPhaseAverage_discarded P R Q h ξ ζ α x y hdiscard, sub_zero,
        idealProductPhase_norm ζ α (idealSelectedProduct_pos hP x) (idealSelectedProduct_pos hR y)]
  have hb := idealKernel_good_bad_bilinear_sq (idealSelectedMass P) (idealSelectedMass R)
    (idealSelectedMass_nonneg P hVP) (idealSelectedMass_nonneg R hVR)
    (idealSelectedMass_sum P hVP) (idealSelectedMass_sum R hVR)
    goodP goodR K hε hk hbad f g
  have he : (∑ x : IdealSelectedLabels P, ∑ y : IdealSelectedLabels R,
      ((idealSelectedMass P x*idealSelectedMass R y : ℝ) : ℂ)*K x y*f x*g y) =
      ∑ x : IdealSelectedLabels P, (idealSelectedMass P x : ℂ)*f x*
        ∑ y : IdealSelectedLabels R, (idealSelectedMass R y : ℂ)*g y*E x y := by
    apply sum_congr rfl
    intro x _
    rw [mul_sum]
    apply sum_congr rfl
    intro y _
    by_cases hz : f x = 0 ∨ g y = 0
    · rcases hz with hx | hy
      · simp only [hx, mul_zero, zero_mul]
      · simp only [hy, mul_zero, zero_mul]
    · rw [show K x y = E x y from ite_eq_right hz, Complex.ofReal_mul]
      ring
  rw [he] at hb
  have hp : (∑ x, if goodP x then 0 else idealSelectedMass P x) =
      idealDiscardedCellMass P h ξ := by
    unfold idealDiscardedCellMass
    apply sum_congr rfl
    intro x _
    by_cases hx : goodP x
    · simp only [hx, ite_true, goodP, not_lt.mpr hx, ite_false]
    · simp only [hx, ite_false, goodP, lt_of_not_ge hx, ite_true]
  have hr : (∑ y, if goodR y then 0 else idealSelectedMass R y) =
      idealDiscardedCellMass R h ξ := by
    unfold idealDiscardedCellMass
    apply sum_congr rfl
    intro y _
    by_cases hy : goodR y
    · simp only [hy, ite_true, goodR, not_lt.mpr hy, ite_false]
    · simp only [hy, ite_false, goodR, lt_of_not_ge hy, ite_true]
  simpa only [hp, hr, E] using hb

end
end ArtinMatthews
