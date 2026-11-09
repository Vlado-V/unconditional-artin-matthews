module

public import ArtinMatthews.SpectralABLDyadicOperator


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set
open scoped ContDiff
noncomputable section

theorem spectralKLIteratedOperator_tsupport (f : ℝ → ℂ) (k : ℕ) :
    tsupport (spectralKLIteratedOperator f k) ⊆ tsupport f := by
  induction k with
  | zero => exact Subset.rfl
  | succ k ih => exact (spectralKLShiftedOperator_tsupport _).trans ih

private theorem spectralKLIteratedOperator_smooth (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ (spectralKLIteratedOperator f k) := by
  induction k with
  | zero => exact hf
  | succ k ih => exact spectralKLShiftedOperator_smooth _ ih

theorem spectralKLIteratedOperator_dyadic_deriv (k J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X Z M : ℝ) (f : ℝ → ℂ),
      0 < X → 1 ≤ Z → X ≤ Z → 0 ≤ M → ContDiff ℝ ∞ f →
      (∀ j ≤ J+2*k, ∀ x ∈ Icc X (2*X), (X/Z)^j*‖iteratedDeriv j f x‖ ≤ M) →
      ∀ j ≤ J, ∀ x ∈ Icc X (2*X),
        (X/Z)^j*‖iteratedDeriv j (spectralKLIteratedOperator f k) x‖ ≤ C*Z^(2*k)*M := by
  induction k generalizing J with
  | zero =>
    refine ⟨1,zero_lt_one,?_⟩
    intro X Z M f hX hZ hXZ hM hf hF j hj x hx
    simpa only [spectralKLIteratedOperator,Nat.mul_zero,pow_zero,one_mul] using
      hF j (by omega) x hx
  | succ k ih =>
    obtain ⟨D,hD,hiter⟩ := ih (J+2)
    obtain ⟨E,hE,hshift⟩ := spectralKLShiftedOperator_dyadic_deriv J
    refine ⟨E*D,mul_pos hE hD,?_⟩
    intro X Z M f hX hZ hXZ hM hf hF j hj x hx
    let g := spectralKLIteratedOperator f k
    have hg : ContDiff ℝ ∞ g := spectralKLIteratedOperator_smooth f hf k
    have hZ' : 0 ≤ Z := zero_le_one.trans hZ
    have hbound := hshift X Z (D*Z^(2*k)*M) g hX hZ hXZ (by positivity) hg
      (hiter X Z M f hX hZ hXZ hM hf (fun j hj x hx => hF j (by omega) x hx)) j hj x hx
    change (X/Z)^j*‖iteratedDeriv j (spectralKLShiftedOperator g) x‖ ≤ _
    refine hbound.trans_eq ?_
    rw [show 2*(k+1) = 2*k+2 by omega,pow_add]
    ring

end
end ArtinMatthews
