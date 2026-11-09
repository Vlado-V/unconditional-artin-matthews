module

public import ArtinMatthews.IdealLogPhase


set_option backward.privateInPublic true
@[expose] public section

/-! Exact separation of the original product phase at a rational
approximation. The Mellin frequency and the additive normalization are unchanged. -/
namespace ArtinMatthews
noncomputable section

def idealProductPhase (ζ α : ℝ) (n m : ℕ) : ℂ :=
  (((n : ℝ)*(m : ℝ) : ℝ) : ℂ)^(Complex.I*(ζ : ℂ)) *
    (Real.fourierChar (α*(n : ℝ)*(m : ℝ)) : ℂ)

theorem idealLogPhase_product (ζ β : ℝ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    idealLogPhase ζ β (Real.log n + Real.log m) = idealProductPhase ζ β n m := by
  rw [idealLogPhase_eq, Real.exp_add, Real.exp_log (by exact_mod_cast hn),
    Real.exp_log (by exact_mod_cast hm)]
  simp only [idealProductPhase, mul_assoc]

theorem idealProductPhase_rational (ζ β : ℝ) (u : ℤ) (r n m : ℕ) :
    idealProductPhase ζ ((u : ℝ)/r + β) n m =
      idealProductPhase ζ β n m * (Real.fourierChar ((u : ℝ)*(n : ℝ)*(m : ℝ)/r) : ℂ) := by
  have he : (Real.fourierChar (((u : ℝ)/r + β)*(n : ℝ)*(m : ℝ)) : ℂ) =
      (Real.fourierChar (β*(n : ℝ)*(m : ℝ)) : ℂ) *
        (Real.fourierChar ((u : ℝ)*(n : ℝ)*(m : ℝ)/r) : ℂ) := by
    simp only [Real.fourierChar_apply]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold idealProductPhase
  rw [he]
  ring

end
end ArtinMatthews
