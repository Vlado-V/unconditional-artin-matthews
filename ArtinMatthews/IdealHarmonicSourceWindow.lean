module

public import ArtinMatthews.IdealHarmonicPrimeWindow
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics


set_option backward.privateInPublic true
@[expose] public section

/-! Actual nonprincipal harmonic prime cancellation throughout the source
exponential window, uniformly over every sharp subinterval. -/
namespace ArtinMatthews
open Filter
open scoped Topology
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealHarmonicPrime_source_window (a c d D : ℝ)
    (ha : 0 ≤ a) (hc : 0 < c) (hd : 0 ≤ d) (hD : 0 ≤ D) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (u v : ℝ),
        (q : ℝ) ≤ L^a → χ ≠ 1 → Real.exp (L^c) ≤ u → u ≤ v →
        v ≤ Real.exp (L^d) → ‖idealHarmonicPrimeInterval χ u v‖ ≤ L^(-D) := by
  let A := 2*a/c
  let P := 2*(D+d+2)/c
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  obtain ⟨C, H₀, hC, hH₀, hwindow⟩ := idealHarmonicPrime_window A P hA hP
  let K := C*(2 + 1/Real.log 2)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 < K := by dsimp [K]; positivity
  have hexp := (Real.tendsto_exp_atTop.comp (tendsto_rpow_atTop hc)).eventually
    (eventually_ge_atTop (2*H₀))
  have hpower := (tendsto_rpow_atTop (show 0 < c/2 by positivity)).eventually
    (eventually_ge_atTop (max 2 (2*Real.log 2)))
  filter_upwards [hexp, hpower, eventually_ge_atTop (max 1 K)] with L hexp hpower hlarge
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hlarge
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have hKle : K ≤ L := (le_max_right _ _).trans hlarge
  have ht2 : 2 ≤ L^(c/2) := (le_max_left _ _).trans hpower
  have htlog : 2*Real.log 2 ≤ L^(c/2) := (le_max_right _ _).trans hpower
  have hsquare : L^c = (L^(c/2))^2 := by
    rw [← Real.rpow_two, ← Real.rpow_mul hL.le]
    congr 1
    ring
  intro q _ χ u v hq hχ hu huv hv
  have hu0 : 0 < u := (Real.exp_pos _).trans_le hu
  have hv0 : 0 < v := hu0.trans_le huv
  have hlogu : L^c ≤ Real.log u := (Real.le_log_iff_exp_le hu0).mpr hu
  have hhalf : L^(c/2) ≤ Real.log (u/2) := by
    rw [Real.log_div hu0.ne' (by norm_num)]
    rw [hsquare] at hlogu
    nlinarith
  have hq' : (q : ℝ) ≤ (Real.log (u/2))^A := by
    have he : (L^(c/2))^A = L^a := by
      rw [← Real.rpow_mul hL.le]
      congr 1
      dsimp [A]
      field_simp
    rw [← he] at hq
    exact hq.trans (Real.rpow_le_rpow (by positivity) hhalf hA)
  have hh := hwindow q χ u v (hexp.trans hu) huv hq' hχ
  have hlogv : Real.log (v+1) ≤ L^d + Real.log 2 := by
    have hv1 : 1 ≤ v := by
      have hp : 0 ≤ L^c := Real.rpow_nonneg hL.le c
      exact (Real.one_le_exp hp).trans (hu.trans huv)
    have hvadd : v+1 ≤ 2*v := by linarith
    calc
      _ ≤ Real.log (2*v) := Real.log_le_log (by positivity) hvadd
      _ = Real.log 2 + Real.log v := Real.log_mul (by norm_num) hv0.ne'
      _ ≤ _ := by have := (Real.log_le_iff_le_exp hv0).mpr hv; linarith
  have hcost : 1 + Real.log (v+1)/Real.log 2 ≤ (2 + 1/Real.log 2)*L^d := by
    have hp : 1 ≤ L^d := Real.one_le_rpow hL1 hd
    have hh := div_le_div_of_nonneg_right hlogv hlog2.le
    have he : (L^d + Real.log 2)/Real.log 2 = L^d/Real.log 2 + 1 := by
      field_simp
    rw [he] at hh
    calc
      _ ≤ 2 + L^d / Real.log 2 := by linarith
      _ ≤ _ := by
        simp only [div_eq_mul_inv]
        nlinarith
  have hdecay : (Real.log (u/2))^(-P) ≤ L^(-(D+d+2)) := by
    have hp := Real.rpow_le_rpow_of_nonpos (show 0 < L^(c/2) by positivity)
      hhalf (neg_nonpos.mpr hP)
    have he : (L^(c/2))^(-P) = L^(-(D+d+2)) := by
      rw [← Real.rpow_mul hL.le]
      congr 1
      dsimp [P]
      field_simp
    exact he ▸ hp
  have hhalfpos : 0 < Real.log (u/2) :=
    lt_of_lt_of_le (by positivity : 0 < L^(c/2)) hhalf
  calc
    _ ≤ C*(1 + Real.log (v+1)/Real.log 2)*(Real.log (u/2))^(-P) := hh
    _ ≤ C*((2 + 1/Real.log 2)*L^d)*L^(-(D+d+2)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hcost hC.le
      · exact hdecay
      · positivity
      · positivity
    _ = (K/L^2)*L^(-D) := by
      dsimp [K]
      have he : -(D+d+2) = -d + (-2) + (-D) := by ring
      rw [he, Real.rpow_add hL, Real.rpow_add hL, Real.rpow_neg hL.le,
        Real.rpow_neg hL.le, Real.rpow_two]
      field_simp
    _ ≤ 1*L^(-D) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply (div_le_one₀ (sq_pos_of_pos hL)).mpr
      nlinarith
    _ = _ := one_mul _

end
end ArtinMatthews
