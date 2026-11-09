module

public import ArtinMatthews.MarkedMinorArcBanRawEntry


set_option backward.privateInPublic true
@[expose] public section

/-! Exact raw-state action of the literal ban difference. -/
noncomputable section
namespace ArtinMatthews

open Matrix

theorem markedRawCleanApply_kernel_sub {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (K L : MarkedRawBackground P pads B → Matrix (MarkedRawCleanFiber P Z) (MarkedRawCleanFiber P Z) ℂ)
    (f : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) :
    markedRawCleanApply ν (K-L) f s = markedRawCleanApply ν K f s-markedRawCleanApply ν L f s := by
  unfold markedRawCleanApply
  simp only [Pi.sub_apply,Matrix.sub_apply,mul_sub,sub_mul,Finset.sum_sub_distrib]

theorem markedRawBanErrorKernel_action_difference {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (f : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) :
    markedRawCleanApply ν (markedRawBanErrorKernel hZ ψ η d₀ Y Q ρ χ) f s =
      markedRawCleanApply ν (markedRawCleanKernel hZ ψ η d₀ Y Q ρ χ) f s-
      markedRawCleanApply ν (markedRawBannedCleanKernel (markedRawCleanKernel hZ ψ η d₀ Y Q ρ χ)) f s := by
  have he : markedRawBanErrorKernel hZ ψ η d₀ Y Q ρ χ =
      markedRawCleanKernel hZ ψ η d₀ Y Q ρ χ-
        markedRawBannedCleanKernel (markedRawCleanKernel hZ ψ η d₀ Y Q ρ χ) := by
    funext bg
    exact markedRawBanErrorKernel_eq_difference hZ ψ η d₀ Y Q ρ χ bg
  rw [he,markedRawCleanApply_kernel_sub]

end ArtinMatthews
