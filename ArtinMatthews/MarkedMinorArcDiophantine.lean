module

public import Mathlib.NumberTheory.DiophantineApproximation.Basic
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-!
# The actual shifted minor-arc rational approximation

The core Dirichlet argument is adapted from the proved
`JointDickman/Amplification/MinorArcApproximation.lean`, with only its unrelated
coefficient imports removed. The final statement is the exact shifted
frequency used by PD (mem:dirichlet-minor), not an assumed approximation.
-/
namespace ArtinMatthews

/-- Real representatives of rational arcs; all integer translates of the
rational numerators are included. -/
def MarkedInRationalArc (θ Q ρ : ℝ) : Prop :=
  ∃ r : ℚ, (r.den : ℝ) ≤ Q ∧ |θ-(r : ℝ)| ≤ ρ

/-- The major arcs in the determinant clean kernel, with source radius `2Q/Y`. -/
def MarkedInMajorArcs (θ Q Y : ℝ) : Prop := MarkedInRationalArc θ Q (2*Q/Y)

/-- Dirichlet approximation outside the rational arcs has a genuinely large
reduced denominator, and retains the `q⁻²` error needed by the Gram bound. -/
theorem marked_minor_rational_approximation {θ Q Y : ℝ}
    (hQ : 0 < Q) (hY : Q ≤ Y) (hminor : ¬MarkedInRationalArc θ Q (Q/Y)) :
    ∃ r : ℚ, Q < (r.den : ℝ) ∧ (r.den : ℝ) ≤ Y/Q ∧
      |θ-(r : ℝ)| ≤ 1/(r.den : ℝ)^2 := by
  have hY0 : 0 < Y := hQ.trans_le hY
  have hratio : 1 ≤ Y/Q := (le_div_iff₀ hQ).mpr (by simpa using hY)
  let n := ⌊Y/Q⌋₊
  have hn : 0 < n := Nat.floor_pos.mpr hratio
  obtain ⟨r,herr,hden⟩ := Real.exists_rat_abs_sub_le_and_den_le θ hn
  have hrpos : (0:ℝ) < r.den := by exact_mod_cast r.pos
  have hden' : (r.den : ℝ) ≤ n := by exact_mod_cast hden
  have hnY : (n : ℝ) ≤ Y/Q := Nat.floor_le (by positivity)
  have happrox : |θ-(r : ℝ)| ≤ Q/Y := by
    refine herr.trans ?_
    calc
      _ ≤ 1/((n : ℝ)+1) := by
        apply one_div_le_one_div_of_le (by positivity)
        have hr1 : (1:ℝ) ≤ r.den := by exact_mod_cast r.pos
        nlinarith
      _ ≤ 1/(Y/Q) := one_div_le_one_div_of_le (by positivity)
        (Nat.lt_floor_add_one (Y/Q)).le
      _ = _ := by field_simp
  refine ⟨r,?_,hden'.trans hnY,?_⟩
  · by_contra h
    exact hminor ⟨r,le_of_not_gt h,happrox⟩
  · refine herr.trans (one_div_le_one_div_of_le (by positivity) ?_)
    nlinarith

/-- The Fourier cutoff shift of size at most `Q/(2Y)` stays outside arcs
of radius `Q/Y` when the original phase is outside the source major arcs. -/
theorem marked_minor_shift_outside {θ t Q Y : ℝ} (hQ : 0 < Q) (hY : 0 < Y)
    (hminor : ¬MarkedInMajorArcs θ Q Y) (ht : |t| ≤ Q/2) :
    ¬MarkedInRationalArc (θ+t/Y) Q (Q/Y) := by
  rintro ⟨r,hr,hd⟩
  apply hminor
  refine ⟨r,hr,?_⟩
  have hshift : |t/Y| ≤ (Q/2)/Y := by
    rw [abs_div,abs_of_pos hY]
    exact div_le_div_of_nonneg_right ht hY.le
  calc
    |θ-(r : ℝ)| = |((θ+t/Y)-(r : ℝ))-t/Y| := by congr 1; ring
    _ ≤ |(θ+t/Y)-(r : ℝ)|+|t/Y| := abs_sub _ _
    _ ≤ Q/Y+(Q/2)/Y := add_le_add hd hshift
    _ = ((3/2)*Q)/Y := by ring
    _ ≤ 2*Q/Y := div_le_div_of_nonneg_right (by linarith) hY.le

/-- The actual shifted minor frequency has the reduced integer numerator
and denominator required by the determinant Gram estimate. -/
theorem marked_minor_shift_reduced_approximation {θ t Q Y : ℝ}
    (hQ : 0 < Q) (hY : Q ≤ Y) (hminor : ¬MarkedInMajorArcs θ Q Y)
    (ht : |t| ≤ Q/2) :
    ∃ (a : ℤ) (q : ℕ), 0 < q ∧ IsCoprime a (q : ℤ) ∧
      Q < (q : ℝ) ∧ (q : ℝ) ≤ Y/Q ∧
      |(θ+t/Y)-(a : ℝ)/q| ≤ 1/(q : ℝ)^2 := by
  obtain ⟨r,hrQ,hrY,hrap⟩ := marked_minor_rational_approximation hQ hY
    (marked_minor_shift_outside hQ (hQ.trans_le hY) hminor ht)
  refine ⟨r.num,r.den,r.pos,?_,hrQ,hrY,?_⟩
  · apply Int.isCoprime_iff_gcd_eq_one.mpr
    simpa only [Int.gcd_def,Int.natAbs_natCast] using r.reduced.gcd_eq_one
  · simpa only [Rat.cast_def] using hrap

end ArtinMatthews
