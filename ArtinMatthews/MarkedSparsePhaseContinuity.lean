module

public import ArtinMatthews.MarkedSparsePhaseKernel


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

theorem markedDyadicPolynomial_continuous (L R : ℕ) (U : ℝ) (a : ℕ → ℂ) :
    Continuous (markedDyadicPolynomial L R U a) := by
  unfold markedDyadicPolynomial markedPrimePhase
  fun_prop

theorem markedDyadicPolynomial_norm_sq_continuous (L R : ℕ) (U : ℝ) (a : ℕ → ℂ) :
    Continuous (fun t => ‖markedDyadicPolynomial L R U a t‖^2) :=
  (markedDyadicPolynomial_continuous L R U a).norm.pow 2

end ArtinMatthews
