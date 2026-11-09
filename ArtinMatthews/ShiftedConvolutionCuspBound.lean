module

public import ArtinMatthews.ShiftedConvolutionAbel


set_option backward.privateInPublic true
@[expose] public section

/-! The actual cusp-form bound for the literal coefficient sequence Aρ.
Only sampled cutoff variation and a pointwise cutoff bound remain explicit;
there is no assumed additive cancellation or coefficient mean square. -/

noncomputable section
open Complex UpperHalfPlane Finset AddCircle
open scoped BigOperators

namespace ArtinMatthews

private theorem stdAddChar_mul_nat_fourier (D : ℕ) [NeZero D] (z : ZMod D) (k : ℕ) :
    ZMod.stdAddChar (z * (k : ZMod D)) = fourier (k : ℤ) (ZMod.toAddCircle z) := by
  have he : z * (k : ZMod D) = k • z := by simp [nsmul_eq_mul, mul_comm]
  rw [he]
  change ((ZMod.toAddCircle (k • z)).toCircle : ℂ) =
    (((k : ℤ) • ZMod.toAddCircle z).toCircle : ℂ)
  rw [map_nsmul, natCast_zsmul]

/-- The congruence character translates the additive frequency; its size is unchanged. -/
theorem shiftedConvolutionLeft_eq_translated (S : Finset ℕ) (m3 D : ℕ) [NeZero D]
    (a : ℕ → ℂ) (j : ZMod D) (x : AddCircle (1 : ℝ)) :
    shiftedConvolutionLeft S m3 D a j x =
      ∑ k ∈ S, a k * fourier (k : ℤ)
        (ZMod.toAddCircle (j * (m3 : ZMod D) ^ 2) + (-(m3 : ℤ)) • x) := by
  simp only [shiftedConvolutionLeft, shiftedTrigPolynomial_apply]
  apply sum_congr rfl
  intro k _
  rw [← mul_assoc j, stdAddChar_mul_nat_fourier]
  have hf : fourier (k : ℤ) (ZMod.toAddCircle (j * (m3 : ZMod D) ^ 2) + (-(m3 : ℤ)) • x) =
      fourier (k : ℤ) (ZMod.toAddCircle (j * (m3 : ZMod D) ^ 2)) *
        fourier (-(m3 : ℤ) * k) x := by
    simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]
    congr 2
    rw [smul_smul]
    congr 1
    ring
  rw [hf]
  ring

/-- An explicit squared version of (5.6), before replacing sampled variation
by derivative seminorms. It is uniform in D, both frequencies, and the rho range. -/
theorem weightOne_shiftedConvolution_energy
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 1) (hperiod : (1 : ℝ) ∈ Γ.strictPeriods) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N1 N2 m3 m4 D : ℕ) [NeZero D], 2 ≤ N1 → 0 < m4 →
      ∀ (v1 v2 : ℕ → ℂ) (B2 : ℝ), 0 ≤ B2 →
        (∀ k ∈ range N2, ‖v2 k‖ ≤ B2) → ∀ R : Finset ℤ,
      (∑ r ∈ R, ‖shiftedConvolutionCoeff (range N1) (range N2) m3 m4 D
        (fun k ↦ (qExpansion 1 f).coeff k * v1 k)
        (fun k ↦ (qExpansion 1 f).coeff k * v2 k) r‖ ^ 2) ≤
          C * N1 * N2 * Real.log (2 * N1) ^ 2 * sampledVariation N1 v1 ^ 2 * B2 ^ 2 := by
  obtain ⟨C1, hC1, hsup⟩ := weightOne_weighted_additive_bound f hperiod
  obtain ⟨C2, hC2, hsquare⟩ := weightOne_sum_norm_sq_le f hperiod
    (fun k ↦ (qExpansion 1 f).coeff k) (fun _ ↦ rfl)
  refine ⟨C1 ^ 2 * C2, by positivity, ?_⟩
  intro N1 N2 m3 m4 D inst hN1 hm4 v1 v2 B2 hB2 hv2 R
  have hvar : 0 ≤ sampledVariation N1 v1 := by
    unfold sampledVariation
    positivity
  have hlog : 0 ≤ Real.log (2 * (N1 : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2*N1))
  have hb := shiftedConvolution_energy_le (range N1) (range N2) m3 m4 D hm4
    (fun k ↦ (qExpansion 1 f).coeff k * v1 k)
    (fun k ↦ (qExpansion 1 f).coeff k * v2 k)
    (C1 * Real.sqrt N1 * Real.log (2 * N1) * sampledVariation N1 v1)
    (by positivity) (fun j x ↦ by
      rw [shiftedConvolutionLeft_eq_translated]
      exact hsup N1 hN1 v1 _) R
  have hsecond : (∑ k ∈ range N2, ‖(qExpansion 1 f).coeff k * v2 k‖ ^ 2) ≤
      B2 ^ 2 * (C2 * N2) := by
    calc
      _ ≤ ∑ k ∈ range N2, B2 ^ 2 * ‖(qExpansion 1 f).coeff k‖ ^ 2 := by
        apply sum_le_sum
        intro k hk
        rw [norm_mul, mul_pow, mul_comm]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hv2 k hk) 2) (sq_nonneg _)
      _ = B2 ^ 2 * ∑ k ∈ range N2, ‖(qExpansion 1 f).coeff k‖ ^ 2 := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hsquare N2) (sq_nonneg _)
  apply hb.trans
  calc
    _ ≤ (C1 * Real.sqrt N1 * Real.log (2 * N1) * sampledVariation N1 v1) ^ 2 *
        (B2 ^ 2 * (C2 * N2)) := mul_le_mul_of_nonneg_left hsecond (sq_nonneg _)
    _ = _ := by rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N1)]; ring

end ArtinMatthews
