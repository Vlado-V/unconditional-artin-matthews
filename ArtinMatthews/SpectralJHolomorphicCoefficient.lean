module

public import ArtinMatthews.SpectralJOddSynthesis
public import Mathlib.Tactic.FieldSimp


set_option backward.privateInPublic true
@[expose] public section

/-! The source holomorphic coefficient uses the actual normalized Petersson
factor 2π i^(-k). Its weight-two contribution keeps the negative sign. -/
noncomputable section
open Set Complex

namespace ArtinMatthews

def spectralJHolomorphicCoefficient (f : ℝ → ℂ) (k : ℕ) : ℂ :=
  (((k-1 : ℕ) : ℂ)/(Real.pi : ℂ))*I^(k : ℤ)*spectralJDiscreteCoefficient f (k-1)

theorem spectralJHolomorphicCoefficient_petersson_factor (f : ℝ → ℂ) (k : ℕ) :
    spectralJHolomorphicCoefficient f k*(2*(Real.pi : ℂ)*I^(-(k : ℤ))) =
      2*((k-1 : ℕ) : ℂ)*spectralJDiscreteCoefficient f (k-1) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI : I^(k : ℤ)*I^(-(k : ℤ)) = 1 := by
    rw [zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ I_ne_zero)]
  calc
    _ = (2*((k-1 : ℕ) : ℂ)*spectralJDiscreteCoefficient f (k-1))*
        (I^(k : ℤ)*I^(-(k : ℤ))) := by
      unfold spectralJHolomorphicCoefficient
      field_simp [hπ] <;> ring
    _ = _ := by rw [hI,mul_one]

theorem spectralJHolomorphicCoefficient_even_eq (f : ℝ → ℂ) (n : ℕ) :
    spectralJHolomorphicCoefficient f (2*n+2) =
      (-1 : ℂ)^(n+1)*(((2*n+1 : ℕ) : ℂ)/(Real.pi : ℂ))*
        spectralJDiscreteCoefficient f (2*n+1) := by
  have hk : 2*n+2-1 = 2*n+1 := by omega
  have hI : I^((2*n+2 : ℕ) : ℤ) = (-1 : ℂ)^(n+1) := by
    rw [zpow_natCast, show 2*n+2 = 2*(n+1) by omega, pow_mul, I_sq]
  rw [spectralJHolomorphicCoefficient,hk,hI]
  ring

theorem spectralJHolomorphicCoefficient_two (f : ℝ → ℂ) :
    spectralJHolomorphicCoefficient f 2 = -spectralJDiscreteCoefficient f 1/(Real.pi : ℂ) := by
  have h := spectralJHolomorphicCoefficient_even_eq f 0
  norm_num at h
  rw [h]
  ring

theorem spectralJHolomorphicCoefficient_odd_term (f : ℝ → ℂ) (n : ℕ) (x : ℝ) :
    spectralJHolomorphicCoefficient f (2*n+2)*
        (2*(Real.pi : ℂ)*I^(-((2*n+2 : ℕ) : ℤ)))*
        Complex.besselJ ((2*n+1 : ℕ) : ℂ) (x : ℂ) =
      spectralJOddSynthesisTerm f n x := by
  rw [spectralJHolomorphicCoefficient_petersson_factor, show 2*n+2-1 = 2*n+1 by omega]
  rfl

theorem spectralJHolomorphicCoefficient_synthesis_summable (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) (x : ℝ) :
    Summable (fun n : ℕ => ‖spectralJHolomorphicCoefficient f (2*n+2)*
      (2*(Real.pi : ℂ)*I^(-((2*n+2 : ℕ) : ℤ)))*
        Complex.besselJ ((2*n+1 : ℕ) : ℂ) (x : ℂ)‖) := by
  simpa only [spectralJHolomorphicCoefficient_odd_term] using spectralJOddSynthesis_summable_norm f hf hc hp x

theorem spectralJHolomorphicCoefficient_synthesis_eq_odd (f : ℝ → ℂ) (x : ℝ) :
    (∑' n : ℕ, spectralJHolomorphicCoefficient f (2*n+2)*
      (2*(Real.pi : ℂ)*I^(-((2*n+2 : ℕ) : ℤ)))*
        Complex.besselJ ((2*n+1 : ℕ) : ℂ) (x : ℂ)) = spectralJOddSynthesis f x := by
  simp only [spectralJHolomorphicCoefficient_odd_term,spectralJOddSynthesis]

end ArtinMatthews
