module

public import ArtinMatthews.IdealLabelOperator


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
noncomputable section

/-- The spectral derivative multiplier factors at the literal natural product. -/
theorem giantSignedTotalD_cpow (d D : ℕ) (ζ : ℝ) :
    ((d * D : ℕ) : ℂ) ^ ((ζ : ℂ) * Complex.I) =
      (d : ℂ) ^ ((ζ : ℂ) * Complex.I) * (D : ℂ) ^ ((ζ : ℂ) * Complex.I) := by
  simpa only [Nat.cast_mul] using
    Complex.natCast_mul_natCast_cpow d D ((ζ : ℂ) * Complex.I)

/-- The original additive frequency scales by the fixed small product. -/
theorem idealAdditivePhase_totalD (θ : ℝ) (d D : ℕ) :
    idealAdditivePhase θ (d * D) = idealAdditivePhase (θ * (d : ℝ)) D := by
  unfold idealAdditivePhase
  congr 1
  push_cast
  ring

/-- Exact separation of both original phase factors at the total product. -/
theorem giantSignedTotalD_multiplier (θ ζ : ℝ) (d D : ℕ) :
    ((d * D : ℕ) : ℂ) ^ ((ζ : ℂ) * Complex.I) * idealAdditivePhase θ (d * D) =
      (d : ℂ) ^ ((ζ : ℂ) * Complex.I) *
        ((D : ℂ) ^ ((ζ : ℂ) * Complex.I) * idealAdditivePhase (θ * (d : ℝ)) D) := by
  rw [giantSignedTotalD_cpow, idealAdditivePhase_totalD]
  ring

/-- The fixed positive small product contributes a unit-modulus multiplier. -/
theorem giantSignedSmallD_cpow_norm (d : ℕ) (hd : 0 < d) (ζ : ℝ) :
    ‖(d : ℂ) ^ ((ζ : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_natCast_cpow_of_pos hd]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, mul_zero, zero_mul, sub_self, Real.rpow_zero]

end
end ArtinMatthews
