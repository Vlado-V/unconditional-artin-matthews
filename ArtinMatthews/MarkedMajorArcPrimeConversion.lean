module

public import ArtinMatthews.MarkedMajorArcPartialSummation


set_option backward.privateInPublic true
@[expose] public section

/-! Conversion from actual character Mangoldt prefix bounds to the actual
prime polynomial, including all higher prime powers and logarithmic weights. -/
namespace ArtinMatthews

open Finset
open scoped BigOperators

noncomputable def markedMajorPrimeSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t u v : ℝ) : ℂ :=
  ∑ p ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime,
    χ (p:ZMod q)*(p:ℂ)^(-1+(t:ℂ)*Complex.I)

lemma marked_major_prime_log_cancel {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) {p : ℕ} (hp : p.Prime) :
    ((Real.log p)⁻¹:ℝ)*(markedMajorMangoldt χ t p) =
      χ (p:ZMod q)*(p:ℂ)^(-1+(t:ℂ)*Complex.I) := by
  have hlog : Real.log p ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  rw [marked_major_mangoldt_prime_term χ t hp,Complex.ofReal_inv]
  have hlogC : (Real.log p:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog
  field_simp

/-- A concrete conversion with only a sharp Mangoldt-prefix bound as input.
The unconditional analytic theorem supplies this input; the conversion itself
adds the explicitly proved prime-power error and a factor of three. -/
theorem marked_major_prime_interval_of_mangoldt_prefix {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) {u v D : ℝ}
    (hu : 1 ≤ u) (hlog : 1 ≤ Real.log u) (huv : u ≤ v) (hvu : v ≤ 2*u)
    (hD : 0 ≤ D)
    (hprefix : ∀ w ∈ Set.Icc u v,
      ‖∑ n ∈ Ioc ⌊u⌋₊ ⌊w⌋₊, markedMajorMangoldt χ t n‖ ≤ D) :
    ‖markedMajorPrimeSum χ t u v‖ ≤ 3*(D+(2*Real.sqrt v*Real.log v)/u) := by
  classical
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := hu0.trans_le huv
  have hlogv : 0 ≤ Real.log v := Real.log_nonneg (hu.trans huv)
  let a : ℕ → ℂ := fun n => if n.Prime then markedMajorMangoldt χ t n else 0
  have hE : 0 ≤ D+(2*Real.sqrt v*Real.log v)/u := by positivity
  have hpref (w : ℝ) (hw : w ∈ Set.Icc u v) :
      ‖∑ n ∈ Ioc ⌊u⌋₊ ⌊w⌋₊, a n‖ ≤ D+(2*Real.sqrt v*Real.log v)/u := by
    have he : (∑ n ∈ Ioc ⌊u⌋₊ ⌊w⌋₊, a n) =
        ∑ n ∈ (Ioc ⌊u⌋₊ ⌊w⌋₊).filter Nat.Prime, markedMajorMangoldt χ t n := by
      rw [sum_filter]
    rw [he]
    have hrem := marked_major_prime_power_interval_error χ t hu hw.1
    have hlogw : 0 ≤ Real.log w := Real.log_nonneg (hu.trans hw.1)
    have hpow : (2*Real.sqrt w*Real.log w)/u ≤ (2*Real.sqrt v*Real.log v)/u := by
      gcongr <;> first | exact hw.2 | exact hu0.trans_le hw.1
    have hh := (norm_sub_le
      (∑ n ∈ Ioc ⌊u⌋₊ ⌊w⌋₊, markedMajorMangoldt χ t n)
      ((∑ n ∈ Ioc ⌊u⌋₊ ⌊w⌋₊, markedMajorMangoldt χ t n)-
        ∑ n ∈ (Ioc ⌊u⌋₊ ⌊w⌋₊).filter Nat.Prime, markedMajorMangoldt χ t n)).trans
      (add_le_add (hprefix w hw) (hrem.trans hpow))
    simpa only [sub_sub_cancel] using hh
  have hh := marked_log_weight_interval_bound a hu0 hlog huv hvu hE hpref
  have he : (∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, ((Real.log n)⁻¹:ℝ)*(a n)) =
      markedMajorPrimeSum χ t u v := by
    rw [markedMajorPrimeSum,sum_filter]
    apply sum_congr rfl
    intro n hn
    by_cases hp : n.Prime
    · simp only [a,ite_eq_left hp]
      exact marked_major_prime_log_cancel χ t hp
    · simp [a,hp]
  rwa [he] at hh

end ArtinMatthews
