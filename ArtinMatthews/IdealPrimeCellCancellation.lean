module

public import ArtinMatthews.IdealPrimeCellInterval
public import ArtinMatthews.IdealSelectedLabels
public import ArtinMatthews.MarkedBonferroniTail


set_option backward.privateInPublic true
@[expose] public section

/-! Siegel--Walfisz cancellation after the actual prime-band and log-cell
restrictions, with the band's harmonic normalizer retained. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable

def idealHarmonicPrimeCell {q : ℕ} (χ : DirichletCharacter ℂ q)
    (P : Finset ℕ) (h : ℝ) (r : ℕ) (j : ℤ) : ℂ :=
  ∑ p : ↥P, if idealPrimeCellIndex h r p.val = j then
    (markedHarmonicAtom P p : ℂ) * χ (p.val : ZMod q) else 0

theorem idealHarmonicPrimeCell_eq {q : ℕ} (χ : DirichletCharacter ℂ q)
    (P : Finset ℕ) (h : ℝ) (r : ℕ) (j : ℤ) :
    idealHarmonicPrimeCell χ P h r j = (bandReciprocalMass P : ℂ)⁻¹ *
      ∑ p ∈ idealPrimeCellSet P h r j, (p : ℂ)⁻¹ * χ (p : ZMod q) := by
  unfold idealHarmonicPrimeCell
  change (∑ p : ↥P, (fun n : ℕ => if idealPrimeCellIndex h r n = j then
    (((1/(n : ℝ))/bandReciprocalMass P : ℝ) : ℂ) * χ (n : ZMod q) else 0) p.val) = _
  calc
    _ = ∑ p ∈ P, if idealPrimeCellIndex h r p = j then
        (((1/(p : ℝ))/bandReciprocalMass P : ℝ) : ℂ) * χ (p : ZMod q) else 0 :=
      sum_coe_sort P _
    _ = _ := by
      rw [idealPrimeCellSet, sum_filter, mul_sum]
      apply sum_congr rfl
      intro p _
      split_ifs
      · simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
        ring
      · exact (mul_zero _).symm

theorem idealPrimeCell_raw_source_bound (a c d D : ℝ)
    (ha : 0 ≤ a) (hc : 0 < c) (hd : 0 ≤ d) (hD : 0 ≤ D) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        (q : ℝ) ≤ L^a → χ ≠ 1 →
        ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) → IdealPrimeInterval P →
        (∀ p ∈ P, Real.exp (L^c) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (L^d)) →
        ∀ (h : ℝ), 0 < h → ∀ (r : ℕ), 0 < r → ∀ j : ℤ,
          ‖∑ p ∈ idealPrimeCellSet P h r j, (p : ℂ)⁻¹ * χ (p : ZMod q)‖ ≤
            L^(-D) + Real.exp (-(L^c)) := by
  filter_upwards [idealHarmonicPrime_source_window a c d D ha hc hd hD,
    eventually_gt_atTop (0 : ℝ)] with L hwindow hL
  intro q _ χ hq hχ P hP hinterval hbounds h hh r hr j
  by_cases hne : (idealPrimeCellSet P h r j).Nonempty
  · let S := idealPrimeCellSet P h r j
    let m := S.min' hne
    let n := S.max' hne
    have hmS : m ∈ S := min'_mem S hne
    have hnS : n ∈ S := max'_mem S hne
    have hmP : m ∈ P := (mem_filter.mp hmS).1
    have hnP : n ∈ P := (mem_filter.mp hnS).1
    have hmn : m ≤ n := min'_le S n hnS
    have hm : 0 < m := (hP m hmP).pos
    have heq := idealPrimeCellSet_hull P hP hinterval hh hr j hne
    rw [heq]
    change ‖idealHarmonicPrimeClosed χ m n‖ ≤ _
    have hi := hwindow q χ m n hq hχ (hbounds m hmP).1
      (by exact_mod_cast hmn) (hbounds n hnP).2
    have hboundary : (m : ℝ)⁻¹ ≤ Real.exp (-(L^c)) := by
      rw [Real.exp_neg]
      exact inv_anti₀ (Real.exp_pos _) (hbounds m hmP).1
    exact (idealHarmonicPrimeClosed_norm_le χ hm hmn).trans (add_le_add hi hboundary)
  · have hz := not_nonempty_iff_eq_empty.mp hne
    rw [hz, sum_empty, norm_zero]
    positivity

theorem idealHarmonicPrimeCell_source_bound (a c d D v₀ : ℝ)
    (ha : 0 ≤ a) (hc : 0 < c) (hd : 0 ≤ d) (hD : 0 ≤ D) (hv₀ : 0 < v₀) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        (q : ℝ) ≤ L^a → χ ≠ 1 →
        ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) → IdealPrimeInterval P →
        (∀ p ∈ P, Real.exp (L^c) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (L^d)) →
        v₀ ≤ bandReciprocalMass P →
        ∀ (h : ℝ), 0 < h → ∀ (r : ℕ), 0 < r → ∀ j : ℤ,
          ‖idealHarmonicPrimeCell χ P h r j‖ ≤ L^(-D) := by
  have htail := (rpow_mul_exp_neg_rpow_tendsto (D+1) hc (by norm_num : (0 : ℝ) < 1)).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [idealPrimeCell_raw_source_bound a c d (D+1) ha hc hd (by positivity),
    htail, eventually_ge_atTop (max 1 (2/v₀))] with L hraw htail hlarge
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hlarge
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have hLsize : 2/v₀ ≤ L := (le_max_right _ _).trans hlarge
  have htail' : Real.exp (-(L^c)) ≤ L^(-(D+1)) := by
    have hp : 0 < L^(D+1) := Real.rpow_pos_of_pos hL _
    have hh : Real.exp (-(L^c)) ≤ 1/(L^(D+1)) := by
      apply (le_div_iff₀ hp).mpr
      calc
        _ = L^(D+1)*Real.exp (-(L^c)) := mul_comm _ _
        _ ≤ 1 := by simpa only [neg_one_mul] using htail.le
    simpa only [Real.rpow_neg hL.le, one_div] using hh
  intro q _ χ hq hχ P hP hinterval hbounds hV h hh r hr j
  have hVpos : 0 < bandReciprocalMass P := hv₀.trans_le hV
  have hb := hraw q χ hq hχ P hP hinterval hbounds h hh r hr j
  rw [idealHarmonicPrimeCell_eq, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hVpos]
  calc
    _ ≤ (bandReciprocalMass P)⁻¹ * (L^(-(D+1)) + Real.exp (-(L^c))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ v₀⁻¹ * (2*L^(-(D+1))) := by
      apply mul_le_mul
      · exact inv_anti₀ hv₀ hV
      · linarith
      · positivity
      · positivity
    _ = (2/(v₀*L))*L^(-D) := by
      rw [show -(D+1) = -1 + (-D) by ring, Real.rpow_add hL,
        Real.rpow_neg_one]
      ring
    _ ≤ 1*L^(-D) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply (div_le_one₀ (mul_pos hv₀ hL)).mpr
      simpa only [mul_comm] using (div_le_iff₀ hv₀).mp hLsize
    _ = _ := one_mul _

end
end ArtinMatthews
