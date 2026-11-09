module

public import ArtinMatthews.MarkedMajorArcPerron
public import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterPositivity


set_option backward.privateInPublic true
@[expose] public section

/-! The actual twisted von Mangoldt polynomial and its logarithmic-derivative
Perron formula, with the `n⁻¹` normalization and the exact frequency sign. -/
namespace ArtinMatthews

open Complex MeasureTheory Erdos970 OAI.TwoPointCorrelations
open scoped LSeries.notation

noncomputable def markedMajorMangoldt {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) (n : ℕ) : ℂ :=
  mrtCharacterMangoldtTwist χ n * (n:ℂ)^(-(1-(t:ℂ)*Complex.I))

noncomputable def markedMajorMangoldtIntegrand {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (x t : ℝ) (s : ℂ) : ℂ :=
  (-deriv (DirichletCharacter.LFunction χ) (s+(1-(t:ℂ)*Complex.I)) /
    DirichletCharacter.LFunction χ (s+(1-(t:ℂ)*Complex.I))) * markedPerronKernel x s

lemma marked_major_mangoldt_term {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) (s : ℂ) (n : ℕ) :
    LSeries.term (markedMajorMangoldt χ t) s n =
      LSeries.term (mrtCharacterMangoldtTwist χ) (s+(1-(t:ℂ)*Complex.I)) n := by
  by_cases hn : n=0
  · simp [hn]
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
    markedMajorMangoldt, Complex.cpow_neg, Complex.cpow_add _ _ hnC]
  ring

lemma marked_major_mangoldt_summable {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) {s : ℂ} (hs : 0 < s.re) :
    LSeriesSummable (markedMajorMangoldt χ t) s := by
  have ht : 1 < (s+(1-(t:ℂ)*Complex.I)).re := by simp; linarith
  have hh := χ.LSeriesSummable_twist_vonMangoldt ht
  exact hh.congr (fun n => (marked_major_mangoldt_term χ t s n).symm)

lemma marked_major_mangoldt_LSeries {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) {s : ℂ} (hs : 0 < s.re) :
    LSeries (markedMajorMangoldt χ t) s =
      -deriv (DirichletCharacter.LFunction χ) (s+(1-(t:ℂ)*Complex.I)) /
        DirichletCharacter.LFunction χ (s+(1-(t:ℂ)*Complex.I)) := by
  have ht : 1 < (s+(1-(t:ℂ)*Complex.I)).re := by simp; linarith
  rw [← mrtCharacter_twisted_series_logderiv χ ht]
  exact tsum_congr (marked_major_mangoldt_term χ t s)

/-- The finite, genuinely twisted Mangoldt sum equals the actual analytic
Perron integral. This does not assume a prime-number estimate. -/
theorem marked_major_mangoldt_perron {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) {x σ : ℝ}
    (hx : 0 < x) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    VerticalIntegral' (markedMajorMangoldtIntegrand χ x t) σ =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        markedMajorMangoldt χ t n * markedMellinTriangle ((n:ℝ)/x) := by
  have he := marked_perron_finite_sum (markedMajorMangoldt χ t) hx hσ hσ1
    (marked_major_mangoldt_summable χ t (by simpa using hσ))
  rw [← he]
  unfold VerticalIntegral' VerticalIntegral
  congr 2
  apply integral_congr_ae
  filter_upwards [] with y
  rw [markedMajorMangoldtIntegrand,
    marked_major_mangoldt_LSeries χ t (by simpa using hσ)]

end ArtinMatthews
