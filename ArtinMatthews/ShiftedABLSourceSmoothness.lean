module

public import ArtinMatthews.ShiftedSourceBessel
public import ArtinMatthews.ShiftedSourceLogSeparation


set_option backward.privateInPublic true
@[expose] public section

/-! The two actual weight-one sources have fixed normalized derivative and
logarithmic Fourier moment constants. The first source uses the prescribed
sequence of derivative constants of its cutoff. The second is the fixed
plateau. -/

noncomputable section

open Complex MeasureTheory Set OAI
open scoped ContDiff

namespace ArtinMatthews

/-- The first source uses only the fixed constants in
`‖g⁽ʲ⁾‖ ≤ Cg j / T^j`. Both the circle-denominator derivatives and the
separated integral have constants independent of every source and dual scale. -/
theorem shiftedABLSourceTest_bounds {ι : Type*} [Fintype ι]
    (V : ι → ℝ → ℂ) (a M : ι → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hVwindow : ∀ j z, V j z ≠ 0 → |z| ≤ M j)
    (A J : ℕ) (Cg : ℕ → ℝ) (hCg : ∀ n, 0 ≤ Cg n) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (g : ℝ → ℂ), ContDiff ℝ ∞ g → ∀ (T m : ℝ), 0 < T → 0 < m →
        Function.support g ⊆ Icc T (2*T) → 1 ≤ m*T →
        (∀ n, ∀ x : ℝ, ‖iteratedDeriv n g x‖ ≤ Cg n/T^n) →
        (∀ (j : ℕ) (x : ℝ), ‖iteratedDeriv j (shiftedSourceTest g m) x‖ ≤ Cg j/(m*T)^j) ∧
        (∀ (x q : ℝ), 0 < x → 0 < q → ∀ j ≤ J,
          (1+(m*T)*(x/q^2))^A * ‖LocalLogFourier.eulerDeriv
            (fun z ↦ weightOneBesselTransform (shiftedSourceTest g m) (x/z^2)) j q‖
            ≤ 2^j*C*(m*T)) ∧
        (∀ R : ℝ, 0 < R → ∃ b : SchwartzMap ℝ ℂ,
          (∀ y : ι → ℝ, (∏ j : ι, V j (y j)) *
            weightOneBesselTransform (shiftedSourceTest g m) (R*Real.exp (∑ j : ι, a j*y j)) =
              ∫ t : ℝ, (∏ j : ι, V j (y j)*FourierBridge.logPhase t (a j*y j))*b t) ∧
          (1+(m*T)*R)^A * (∫ t : ℝ, (1+‖t‖)^J*‖b t‖) ≤ C*(m*T)) := by
  obtain ⟨L₁,C₁,hC₁,hdenom⟩ := shiftedSourceTest_bessel_denominator_bound A J
  obtain ⟨L₂,hsep⟩ := shiftedSourceTest_log_separation V a M hM hVwindow A J
  let G := ∑ n ∈ Finset.range (max L₁ L₂ + 1), Cg n
  have hG : 0 ≤ G := Finset.sum_nonneg (fun n _ => hCg n)
  have hG_ge (n : ℕ) (hn : n ≤ max L₁ L₂) : Cg n ≤ G :=
    Finset.single_le_sum (fun k _ => hCg k) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
  obtain ⟨C₂,hC₂,hsep⟩ := hsep G hG
  let C := C₁*G+C₂+1
  have hC₁G : 0 ≤ C₁*G := mul_nonneg hC₁.le hG
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro g hg T m hT hm hsupport hscale hderiv
  refine ⟨fun j x => shiftedSourceTest_derivative_bound g hg m T (Cg j) hm hT j (hderiv j) x, ?_⟩
  have hD (n : ℕ) (hn : n ≤ max L₁ L₂) (x : ℝ) :
      ‖iteratedDeriv n g x‖ ≤ G/T^n :=
    (hderiv n x).trans (div_le_div_of_nonneg_right (hG_ge n hn) (pow_nonneg hT.le _))
  constructor
  · intro x q hx hq j hj
    apply (hdenom g hg T m G hT hm hG hsupport hscale
      (fun n hn => hD n (hn.trans (le_max_left _ _))) x q hx hq j hj).trans
    calc
      2^j*C₁*G*(m*T) = 2^j*(C₁*G)*(m*T) := by ring
      _ ≤ 2^j*C*(m*T) := by gcongr; dsimp [C]; linarith
  · intro R hR
    obtain ⟨b,hb,hbound⟩ := hsep g hg T m hT hm hsupport hscale
      (fun n hn => hD n (hn.trans (le_max_right _ _))) R hR
    exact ⟨b,hb,hbound.trans (mul_le_mul_of_nonneg_right
      (by dsimp [C]; linarith : C₂ ≤ C) (mul_nonneg hm.le hT.le))⟩

/-- The constructed second source requires no cutoff derivative constants
as input. -/
theorem shiftedABLSourceMajorant_bounds {ι : Type*} [Fintype ι]
    (V : ι → ℝ → ℂ) (a M : ι → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hVwindow : ∀ j z, V j z ≠ 0 → |z| ≤ M j) (A J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T m : ℝ), 0 < T → 0 < m → 1 ≤ m*T →
      (∀ j ≤ J, ∀ x : ℝ, ‖iteratedDeriv j (shiftedSourceMajorant m T) x‖ ≤ C/(m*T)^j) ∧
      (∀ (x q : ℝ), 0 < x → 0 < q → ∀ j ≤ J,
        (1+(m*T)*(x/q^2))^A * ‖LocalLogFourier.eulerDeriv
          (fun z ↦ weightOneBesselTransform (shiftedSourceMajorant m T) (x/z^2)) j q‖
          ≤ 2^j*C*(m*T)) ∧
      (∀ R : ℝ, 0 < R → ∃ b : SchwartzMap ℝ ℂ,
        (∀ y : ι → ℝ, (∏ j : ι, V j (y j)) *
          weightOneBesselTransform (shiftedSourceMajorant m T) (R*Real.exp (∑ j : ι, a j*y j)) =
            ∫ t : ℝ, (∏ j : ι, V j (y j)*FourierBridge.logPhase t (a j*y j))*b t) ∧
        (1+(m*T)*R)^A * (∫ t : ℝ, (1+‖t‖)^J*‖b t‖) ≤ C*(m*T)) := by
  obtain ⟨C₁,hC₁,hdenom⟩ := shiftedSourceMajorant_bessel_denominator_bound A J
  obtain ⟨C₂,hC₂,hsep⟩ := shiftedSourceMajorant_log_separation V a M hM hVwindow A J
  have hcompact : HasCompactSupport shiftedSourcePlateau :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc shiftedSourcePlateau_support
  obtain ⟨C₃,hC₃,hplateau⟩ := hcompact.exists_bound_iteratedFDeriv shiftedSourcePlateau_smooth J
  let C := C₁+C₂+C₃
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro T m hT hm hscale
  refine ⟨?_, ?_⟩
  · intro j hj x
    have hb (y : ℝ) : ‖iteratedDeriv j shiftedSourcePlateau y‖ ≤ C/(1 : ℝ)^j := by
      rw [one_pow, div_one]
      apply le_trans _ (show C₃ ≤ C by dsimp [C]; linarith)
      simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hplateau j hj y
    change ‖iteratedDeriv j (shiftedSourceTest shiftedSourcePlateau (m*T)) x‖ ≤ C/(m*T)^j
    simpa only [mul_one] using shiftedSourceTest_derivative_bound shiftedSourcePlateau
      shiftedSourcePlateau_smooth (m*T) 1 C (mul_pos hm hT) zero_lt_one j hb x
  constructor
  · intro x q hx hq j hj
    apply (hdenom T m hT hm hscale x q hx hq j hj).trans
    gcongr
    dsimp [C]
    linarith
  · intro R hR
    obtain ⟨b,hb,hbound⟩ := hsep T m hT hm hscale R hR
    exact ⟨b,hb,hbound.trans (mul_le_mul_of_nonneg_right
      (by dsimp [C]; linarith : C₂ ≤ C) (mul_nonneg hm.le hT.le))⟩

end ArtinMatthews
