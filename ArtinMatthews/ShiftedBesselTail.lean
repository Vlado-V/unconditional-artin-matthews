module

public import ArtinMatthews.ShiftedBesselScale
public import ArtinMatthews.ShiftedVoronoiSourceSummation


set_option backward.privateInPublic true
@[expose] public section

/-! Arbitrary-power tails beyond the actual dual length Q/K, uniformly in
the scaling parameters. Coefficient convergence is supplied by the genuine
cusp-form mean square through its absolutely convergent s=2 Dirichlet series. -/

noncomputable section
open Complex UpperHalfPlane Real Set

namespace ArtinMatthews

private theorem decay_tail_point (A : ℕ) (C K S x L b : ℝ)
    (_hK : 0 < K) (hS : 0 < S) (hx : 0 < x) (hL : 0 < L) (hLx : L ≤ x)
    (hb : 0 ≤ b) (hdecay : (1+x/S)^(A+2)*b ≤ C*K) :
    b ≤ (C*K*S^2*(S/L)^A) / x^2 := by
  have hd : (x/S)^(A+2)*b ≤ C*K := by
    apply le_trans _ hdecay
    gcongr
    linarith
  have hm := mul_le_mul_of_nonneg_right hd (pow_nonneg hS.le (A+2))
  have he : ((x/S)^(A+2)*b)*S^(A+2) = x^(A+2)*b := by
    rw [div_pow]
    field_simp
  rw [he] at hm
  have hp : b*x^2*L^A ≤ C*K*S^(A+2) := by
    calc
      _ ≤ b*x^2*x^A := by gcongr
      _ = x^(A+2)*b := by rw [pow_add]; ring
      _ ≤ _ := hm
  have hr : C*K*S^2*(S/L)^A = (C*K*S^(A+2))/L^A := by
    rw [div_pow, pow_add]
    ring
  rw [hr]
  apply (le_div_iff₀ (sq_pos_of_pos hx)).mpr
  exact (le_div_iff₀ (pow_pos hL A)).mpr hp

/-- Uniform absolute tail bound with arbitrary power saving past Q/K.
In the Voronoi formula Q=q². The polynomial prefactor is explicit; the constant
is independent of the scale K, the denominator scale Q, the truncation L and
the additive frequency θ. No tail bound is assumed of the coefficients. -/
theorem weightOne_scaled_bessel_tail
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 1) (hperiod : (1 : ℝ) ∈ Γ.strictPeriods)
    (W : SchwartzMap ℝ ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hWs : Function.support W ⊆ Icc 0 B) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K Q L θ : ℝ), 0 < K → 0 < Q → 0 < L →
      Summable (fun n : ℕ ↦ if L ≤ ((n+1 : ℕ) : ℝ) then
        cuspAdditiveCoeff f θ (n+1) *
          weightOneBesselTransform (fun x ↦ W (x/K)) (((n+1 : ℕ) : ℝ)/Q) else 0) ∧
      (∑' n : ℕ, ‖if L ≤ ((n+1 : ℕ) : ℝ) then
        cuspAdditiveCoeff f θ (n+1) *
          weightOneBesselTransform (fun x ↦ W (x/K)) (((n+1 : ℕ) : ℝ)/Q) else 0‖) ≤
            C*K*(Q/K)^2*((Q/K)/L)^A := by
  obtain ⟨C0,hC0,hdecay⟩ := weightOneBesselTransform_rapid_decay W B hB hWs (A+2)
  let c (n : ℕ) := ‖(qExpansion 1 f).coeff (n+1)‖ / (((n+1 : ℕ) : ℝ)^2)
  have hc : Summable c := by
    have hs := cuspAdditiveCoeff_summable_natSucc f hperiod 0 2 (by norm_num)
    simpa only [norm_cuspAdditiveCoeff, Real.rpow_neg (Nat.cast_nonneg _),
      Real.rpow_two, div_eq_mul_inv, c] using hs
  have hc0 : 0 ≤ ∑' n : ℕ, c n := tsum_nonneg (fun n ↦ by dsimp [c]; positivity)
  refine ⟨C0*(∑' n : ℕ, c n), mul_nonneg hC0 hc0, ?_⟩
  intro K Q L θ hK hQ hL
  let S := Q/K
  have hS : 0 < S := div_pos hQ hK
  let E := C0*K*S^2*(S/L)^A
  have hE : 0 ≤ E := by dsimp [E]; positivity
  let F (n : ℕ) : ℂ := if L ≤ ((n+1 : ℕ) : ℝ) then cuspAdditiveCoeff f θ (n+1) *
    weightOneBesselTransform (fun x ↦ W (x/K)) (((n+1 : ℕ) : ℝ)/Q) else 0
  have hpoint (n : ℕ) : ‖F n‖ ≤ E*c n := by
    dsimp only [F]
    split_ifs with hn
    · have hx : 0 < ((n+1 : ℕ) : ℝ) := by positivity
      have heq : K*(((n+1 : ℕ) : ℝ)/Q) = ((n+1 : ℕ) : ℝ)/S := by
        dsimp [S]
        field_simp
      have hb : (1+((n+1 : ℕ) : ℝ)/S)^(A+2) *
          ‖weightOneBesselTransform (fun x ↦ W (x/K)) (((n+1 : ℕ) : ℝ)/Q)‖ ≤ C0*K := by
        rw [weightOneBesselTransform_dilate W K _ hK, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hK, heq]
        have hh := mul_le_mul_of_nonneg_left (hdecay (((n+1 : ℕ) : ℝ)/S) (div_pos hx hS)) hK.le
        nlinarith
      have ht := decay_tail_point A C0 K S ((n+1 : ℕ) : ℝ) L _ hK hS hx hL hn (norm_nonneg _) hb
      rw [norm_mul, norm_cuspAdditiveCoeff]
      have hm := mul_le_mul_of_nonneg_left ht (norm_nonneg ((qExpansion 1 f).coeff (n+1)))
      dsimp [E, c]
      convert hm using 1
      ring
    · rw [norm_zero]
      exact mul_nonneg hE (by dsimp [c]; positivity)
  have hn : Summable (fun n ↦ ‖F n‖) :=
    Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) hpoint (hc.mul_left E)
  refine ⟨hn.of_norm, ?_⟩
  have ht := hn.tsum_le_tsum hpoint (hc.mul_left E)
  rw [tsum_mul_left] at ht
  convert ht using 1
  dsimp [E, S]
  ring

end ArtinMatthews
