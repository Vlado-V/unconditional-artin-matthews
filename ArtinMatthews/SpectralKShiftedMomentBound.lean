module

public import ArtinMatthews.SpectralKShiftedMomentRatio


set_option backward.privateInPublic true
@[expose] public section

/-! Polynomial spectral growth of the actual shifted K square moments,
with the exact hyperbolic-cosine normalization. -/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

theorem spectralKSquareMoment_nonneg (k : ℕ) (t : ℝ) : 0 ≤ spectralKSquareMoment k t := by
  unfold spectralKSquareMoment
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change (0 : ℝ) ≤ x^(2*k)*(spectralKLRealKernel t x)^2
  exact mul_nonneg (pow_nonneg hx.le _) (sq_nonneg _)

theorem spectralKSquareMoment_succ_bound (k : ℕ) (t : ℝ) :
    spectralKSquareMoment (k+1) t ≤
      ((k : ℝ)+1)^2*(1+t^2)*spectralKSquareMoment k t := by
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hd : 0 < (2*(k : ℝ)+1)*(2*(k : ℝ)+2) := by positivity
  have hr : 4*((k : ℝ)+1/2)^2/((2*(k : ℝ)+1)*(2*(k : ℝ)+2)) ≤ 1 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith
  have hp : ((k : ℝ)+1/2)^2+t^2 ≤ ((k : ℝ)+1)^2*(1+t^2) := by
    have h1 : 1 ≤ ((k : ℝ)+1)^2 := by nlinarith
    have ht := mul_le_mul_of_nonneg_right h1 (sq_nonneg t)
    nlinarith
  rw [spectralKSquareMoment_succ]
  apply mul_le_mul_of_nonneg_right _ (spectralKSquareMoment_nonneg k t)
  calc
    _ = (4*((k : ℝ)+1/2)^2/((2*(k : ℝ)+1)*(2*(k : ℝ)+2)))*(((k : ℝ)+1/2)^2+t^2) := by ring
    _ ≤ ((k : ℝ)+1/2)^2+t^2 := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hr (by positivity : 0 ≤ ((k : ℝ)+1/2)^2+t^2)
    _ ≤ _ := hp

theorem spectralKSquareMoment_polynomial_bound (k : ℕ) (t : ℝ) :
    spectralKSquareMoment k t ≤
      (k.factorial : ℝ)^2*(1+t^2)^k*spectralKSquareMoment 0 t := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      _ ≤ ((k : ℝ)+1)^2*(1+t^2)*spectralKSquareMoment k t := spectralKSquareMoment_succ_bound k t
      _ ≤ ((k : ℝ)+1)^2*(1+t^2)*((k.factorial : ℝ)^2*(1+t^2)^k*spectralKSquareMoment 0 t) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ = _ := by rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ];ring

theorem spectralKShiftedMoment_uniform_bound (k : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hBk : B < (k : ℝ)+1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ t : ℝ, |δ| ≤ B →
      spectralKShiftedMoment k δ t ≤ C*(1+t^2)^k/Real.cosh (Real.pi*t) := by
  obtain ⟨R,hR,hbound⟩ := spectralKShiftedMomentRatio_bound k B hB hBk
  refine ⟨R*(k.factorial : ℝ)^2*Real.pi^2/4,by positivity,?_⟩
  intro δ t hδ
  rw [spectralKShiftedMoment_eq_ratio k δ t (hδ.trans_lt hBk)]
  calc
    _ ≤ R*spectralKSquareMoment k t :=
      mul_le_mul_of_nonneg_right (hbound δ hδ) (spectralKSquareMoment_nonneg k t)
    _ ≤ R*((k.factorial : ℝ)^2*(1+t^2)^k*spectralKSquareMoment 0 t) :=
      mul_le_mul_of_nonneg_left (spectralKSquareMoment_polynomial_bound k t) hR.le
    _ = _ := by rw [spectralKSquareMoment_zero];ring

end ArtinMatthews
