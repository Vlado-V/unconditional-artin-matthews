module

public import ArtinMatthews.AdditiveCuspKernel
public import ArtinMatthews.AdditiveCuspKernelIntegral


set_option backward.privateInPublic true
@[expose] public section

/-!
# Uniform additive partial sums for weight-one cusp forms

This proves the analytic estimate (5.4) for the actual q-expansion coefficients
of an arithmetic weight-one cusp form with period one. The proof uses the
horizontal convolution identity and an explicit logarithmic L¹ bound for the
exponentially weighted Dirichlet kernel. Constructing the cubic theta series
appearing in the paper remains a separate task.
-/

noncomputable section
open scoped BigOperators
open Complex UpperHalfPlane

namespace ArtinMatthews

/-- The compensating Dirichlet kernel has logarithmic L¹ growth. -/
theorem integral_norm_weightedFourierKernel_le (N : ℕ) (hN : 2 ≤ N) :
    (∫ t in (0 : ℝ)..1, ‖weightedFourierKernel N (1 / (N : ℝ)) t‖) ≤
      2 * (Real.exp (2 * Real.pi) + 1) * (1 + Real.log N) := by
  apply integral_norm_le_log_of_symmetric_bounds
    (continuous_weightedFourierKernel N (1 / N)) (by positivity)
    (by exact_mod_cast hN)
  · exact norm_weightedFourierKernel_one_sub N (1 / N)
  · intro t _
    exact norm_weightedFourierKernel_le_flat N (by omega) t
  · intro t ht
    exact norm_weightedFourierKernel_le_reciprocal N (by omega) ht.1 ht.2

/-- The logarithmic kernel estimate is uniform in the additive frequency. -/
theorem integral_norm_weightedFourierKernel_sub_le (N : ℕ) (hN : 2 ≤ N) (θ : ℝ) :
    (∫ t in (0 : ℝ)..1, ‖weightedFourierKernel N (1 / (N : ℝ)) (θ - t)‖) ≤
      2 * (Real.exp (2 * Real.pi) + 1) * (1 + Real.log N) := by
  rw [integral_norm_sub_eq_of_periodic (weightedFourierKernel_periodic N (1 / N))]
  exact integral_norm_weightedFourierKernel_le N hN

/-- Uniform additive cancellation with the elementary logarithmic factor. -/
theorem weightOne_additive_sum_le_sqrt_mul_one_add_log
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 1) (hperiod : (1 : ℝ) ∈ Γ.strictPeriods) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ θ : ℝ,
      ‖∑ n ∈ Finset.range N, (qExpansion 1 f).coeff n *
        fourier (n : ℤ) (θ : AddCircle (1 : ℝ))‖ ≤
          C * Real.sqrt N * (1 + Real.log N) := by
  obtain ⟨B, hB, hb⟩ := weightOne_additive_sum_le_kernel_integral f hperiod
  refine ⟨B * (2 * (Real.exp (2 * Real.pi) + 1)), by positivity, ?_⟩
  intro N hN θ
  calc
    _ ≤ (B * Real.sqrt N) *
        ∫ t in (0 : ℝ)..1, ‖weightedFourierKernel N (1 / (N : ℝ)) (θ - t)‖ :=
      hb N (by omega) θ
    _ ≤ (B * Real.sqrt N) *
        (2 * (Real.exp (2 * Real.pi) + 1) * (1 + Real.log N)) :=
      mul_le_mul_of_nonneg_left (integral_norm_weightedFourierKernel_sub_le N hN θ)
        (by positivity)
    _ = _ := by ring

/-- Equation (5.4), with a constant independent of the additive frequency and
cutoff, for the actual coefficients of a weight-one cusp form. -/
theorem weightOne_additive_sum_le_sqrt_mul_log
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 1) (hperiod : (1 : ℝ) ∈ Γ.strictPeriods) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ θ : ℝ,
      ‖∑ n ∈ Finset.range N, (qExpansion 1 f).coeff n *
        fourier (n : ℤ) (θ : AddCircle (1 : ℝ))‖ ≤
          C * Real.sqrt N * Real.log (2 * N) := by
  obtain ⟨B, hB, hb⟩ := weightOne_additive_sum_le_sqrt_mul_one_add_log f hperiod
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨B * (1 + 1 / Real.log 2), by positivity, ?_⟩
  intro N hN θ
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlower : Real.log 2 ≤ Real.log (2 * (N : ℝ)) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hone : 1 ≤ Real.log (2 * (N : ℝ)) / Real.log 2 :=
    (le_div_iff₀ hl2).mpr (by simpa using hlower)
  have hmono : Real.log (N : ℝ) ≤ Real.log (2 * (N : ℝ)) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog : 1 + Real.log (N : ℝ) ≤
      (1 + 1 / Real.log 2) * Real.log (2 * (N : ℝ)) := by
    calc
      1 + Real.log (N : ℝ) ≤
          Real.log (2 * (N : ℝ)) / Real.log 2 + Real.log (2 * (N : ℝ)) :=
        add_le_add hone hmono
      _ = _ := by ring
  calc
    _ ≤ B * Real.sqrt N * (1 + Real.log N) := hb N hN θ
    _ ≤ B * Real.sqrt N * ((1 + 1 / Real.log 2) * Real.log (2 * N)) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = _ := by ring

/-- The literal real-cutoff form of (5.4). The sum includes the coefficient at
zero, which vanishes for a cusp form, and all natural indices `n ≤ T`. -/
theorem weightOne_additive_sum_le_real_cutoff
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 1) (hperiod : (1 : ℝ) ∈ Γ.strictPeriods) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T → ∀ θ : ℝ,
      ‖∑ n ∈ Finset.range (⌊T⌋₊ + 1), (qExpansion 1 f).coeff n *
        fourier (n : ℤ) (θ : AddCircle (1 : ℝ))‖ ≤
          C * Real.sqrt T * Real.log (2 * T) := by
  obtain ⟨B, hB, hb⟩ := weightOne_additive_sum_le_sqrt_mul_log f hperiod
  refine ⟨4 * B, by positivity, ?_⟩
  intro T hT θ
  have hT0 : 0 ≤ T := by linarith
  have hN : 2 ≤ ⌊T⌋₊ + 1 := by
    have : 1 ≤ ⌊T⌋₊ := (Nat.one_le_floor_iff _).mpr (by linarith)
    omega
  have hNpos : (0 : ℝ) < (⌊T⌋₊ + 1 : ℕ) := by positivity
  have hNle : ((⌊T⌋₊ + 1 : ℕ) : ℝ) ≤ T + 1 := by
    push_cast
    linarith [Nat.floor_le hT0]
  have hsqrt : Real.sqrt ((⌊T⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt T := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt hT0]
    nlinarith
  have hlog : Real.log (2 * ((⌊T⌋₊ + 1 : ℕ) : ℝ)) ≤ 2 * Real.log (2 * T) := by
    calc
      _ ≤ Real.log ((2 * T) ^ 2) :=
        Real.log_le_log (by positivity) (by nlinarith)
      _ = _ := by rw [Real.log_pow]; norm_num
  have hlogN : 0 ≤ Real.log (2 * ((⌊T⌋₊ + 1 : ℕ) : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * (⌊T⌋₊ + 1)))
  calc
    _ ≤ B * Real.sqrt (⌊T⌋₊ + 1 : ℕ) * Real.log (2 * (⌊T⌋₊ + 1 : ℕ)) :=
      hb (⌊T⌋₊ + 1) hN θ
    _ ≤ B * (2 * Real.sqrt T) * (2 * Real.log (2 * T)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hsqrt hB) hlog hlogN (by positivity)
    _ = _ := by ring

/-- A named coefficient sequence identified with the genuine q-expansion has
the same uniform additive-frequency estimate. -/
theorem weightOne_coefficients_additive_bound
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 1) (hperiod : (1 : ℝ) ∈ Γ.strictPeriods)
    (a : ℕ → ℂ) (hcoeff : ∀ n, a n = (qExpansion 1 f).coeff n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T → ∀ θ : ℝ,
      ‖∑ n ∈ Finset.range (⌊T⌋₊ + 1), a n *
        fourier (n : ℤ) (θ : AddCircle (1 : ℝ))‖ ≤
          C * Real.sqrt T * Real.log (2 * T) := by
  simpa only [hcoeff] using weightOne_additive_sum_le_real_cutoff f hperiod

end ArtinMatthews
