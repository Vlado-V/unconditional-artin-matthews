module

public import ArtinMatthews.HeckeIntervalBoundaryCount
public import ArtinMatthews.HeckePrimeSmoothSums
public import ArtinMatthews.PrimeExtractionTupleBounds


set_option backward.privateInPublic true
@[expose] public section

/-! Exact conversion from the concrete logarithmic cutoff to the literal
integer prime interval, with all coefficient bounds discharged. -/

noncomputable section
namespace ArtinMatthews
open OAI OAI.SevenEighths
open scoped BigOperators Classical

def heckeSharpPrimeSum (η : HeckeFamily.Character) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (m n : ℕ) (t : ℝ) : ℂ :=
  ∑ p ∈ (Finset.Ioc m n).filter Nat.Prime,
    idealThetaCoeff η p*χ p*(p : ℂ)^((t : ℂ)*Complex.I)

def heckePrimePhaseCoefficient (η : HeckeFamily.Character) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) (p : ℕ) : ℂ :=
  if p.Prime then idealThetaCoeff η p*χ p*(p : ℂ)^((t : ℂ)*Complex.I) else 0

theorem heckePrimePhaseCoefficient_norm_le_two (η : HeckeFamily.Character) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) (p : ℕ) :
    ‖heckePrimePhaseCoefficient η χ t p‖ ≤ 2 := by
  unfold heckePrimePhaseCoefficient
  split_ifs with hp
  · have hn : ‖(p : ℂ)^((t : ℂ)*Complex.I)‖ = 1 := by
      rw [← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hp.pos : (0 : ℝ) < p)]
      simp
    rw [norm_mul, hn, mul_one, norm_mul]
    exact (mul_le_mul (idealThetaCoeff_prime_norm_le_two η hp) (χ.norm_le_one _)
      (norm_nonneg _) (by norm_num)).trans_eq (by ring)
  · norm_num

theorem heckeLogInterval_integer_sum (a : ℕ → ℂ) (m n N : ℕ) {H : ℝ}
    (hH : 0 < H) (hm : 0 < m) (hmn : m ≤ n) (hn : n ≤ N) :
    (∑ p ∈ Finset.Icc 1 N, a p*(if Real.log ((m : ℝ)/H)<Real.log ((p : ℝ)/H) ∧
      Real.log ((p : ℝ)/H)≤Real.log ((n : ℝ)/H) then (1 : ℂ) else 0)) =
      ∑ p ∈ Finset.Ioc m n, a p := by
  have he (p : ℕ) (hp : p ∈ Finset.Icc 1 N) :
      (Real.log ((m : ℝ)/H)<Real.log ((p : ℝ)/H) ∧
        Real.log ((p : ℝ)/H)≤Real.log ((n : ℝ)/H)) ↔ m<p ∧ p≤n := by
    have hp0 : 0 < (p : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hp).1
    have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast hm.trans_le hmn
    rw [Real.log_lt_log_iff (div_pos hm0 hH) (div_pos hp0 hH),
      Real.log_le_log_iff (div_pos hp0 hH) (div_pos hn0 hH),
      div_lt_div_iff_of_pos_right hH, div_le_div_iff_of_pos_right hH]
    norm_cast
  have hset : (Finset.Icc 1 N).filter (fun p : ℕ =>
      Real.log ((m : ℝ)/H)<Real.log ((p : ℝ)/H) ∧
        Real.log ((p : ℝ)/H)≤Real.log ((n : ℝ)/H)) = Finset.Ioc m n := by
    ext p
    constructor
    · intro hp
      have h := Finset.mem_filter.mp hp
      exact Finset.mem_Ioc.mpr ((he p h.1).mp h.2)
    · intro hp
      have h := Finset.mem_Ioc.mp hp
      have hpS : p ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, h.2.trans hn⟩
      exact Finset.mem_filter.mpr ⟨hpS, (he p hpS).mpr h⟩
  simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter, hset]

theorem heckeInterval_sharp_comparison (η : HeckeFamily.Character) {q : ℕ}
    (χ : DirichletCharacter ℂ q) {ε H : ℝ} (hε : 0 < ε) (hεh : ε ≤ 1/2)
    (hH : 0 < H) (m n : ℕ) (hmn : m ≤ n) (hmH : H ≤ m) (hnH : (n : ℝ) ≤ 2*H) (t : ℝ) :
    ‖heckeRationalPrimeSmoothSum η χ
      (heckeLogIntervalCutoff ε (Real.log ((m : ℝ)/H)) (Real.log ((n : ℝ)/H))) H t -
      heckeSharpPrimeSum η χ m n t‖ ≤ 32*ε*H+8 := by
  let u := Real.log ((m : ℝ)/H)
  let v := Real.log ((n : ℝ)/H)
  let b := 2*Real.exp 1
  let N := ⌊b*H⌋₊
  have hm0 : 0 < (m : ℝ) := hH.trans_le hmH
  have hm : 0 < m := by exact_mod_cast hm0
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hm.trans_le hmn
  have hu : 0 ≤ u := Real.log_nonneg ((one_le_div hH).mpr hmH)
  have huv : u ≤ v := Real.log_le_log (div_pos hm0 hH)
    ((div_le_div_iff_of_pos_right hH).mpr (by exact_mod_cast hmn))
  have hv : v ≤ Real.log 2 := Real.log_le_log (div_pos hn0 hH) ((div_le_iff₀ hH).mpr hnH)
  have hb : 2 ≤ b := by
    have he : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp (by norm_num)
    dsimp [b]
    linarith
  have hnN : n ≤ N := Nat.le_floor (hnH.trans (mul_le_mul_of_nonneg_right hb hH.le))
  have ha := heckePrimePhaseCoefficient_norm_le_two η χ t
  have hc := heckeLogInterval_finite_boundary_bound hε hεh huv hv hH
    (by norm_num : (0 : ℝ) ≤ 2) (Finset.Icc 1 N) (heckePrimePhaseCoefficient η χ t)
    (fun p hp => (Finset.mem_Icc.mp hp).1) (fun p _ => ha p)
  rw [heckeLogInterval_integer_sum _ m n N hH hm hmn hnN] at hc
  have hfirst : (∑ p ∈ Finset.Icc 1 N,
      heckePrimePhaseCoefficient η χ t p*heckeLogIntervalCutoff ε u v ((p : ℝ)/H)) =
      heckeRationalPrimeSmoothSum η χ (heckeLogIntervalCutoff ε u v) H t := by
    rw [heckeRationalPrimeSmoothSum_eq_finite η χ _ 1 b H t hH
      (heckeLogIntervalCutoff_uniform_support hε (by linarith) hu huv hv)]
    rw [max_eq_right (show 1 ≤ b by linarith), heckeRationalPrimeSum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    unfold heckePrimePhaseCoefficient
    split_ifs <;> ring
  have hsecond : (∑ p ∈ Finset.Ioc m n, heckePrimePhaseCoefficient η χ t p) =
      heckeSharpPrimeSum η χ m n t := by
    rw [heckeSharpPrimeSum, Finset.sum_filter]
    rfl
  rw [hfirst, hsecond] at hc
  exact hc.trans_eq (by ring)

end ArtinMatthews
