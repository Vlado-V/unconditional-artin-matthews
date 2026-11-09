module

public import ArtinMatthews.SpectralJHolomorphicCoefficient
public import ArtinMatthews.SpectralPeterssonGram


set_option backward.privateInPublic true
@[expose] public section

/-! The source holomorphic weight multiplies the actual normalized, true-width
Petersson term to give the odd part of the forward-J inversion. The algebra
includes weight two. The Gram theorem retains its own weight hypotheses. -/
noncomputable section
open Set Complex
open scoped MatrixGroups

namespace ArtinMatthews

theorem spectralJHolomorphicCoefficient_gram_modulus (f : ℝ → ℂ)
    (N : ℕ) [NeZero N] (b a : SL(2, ℤ)) (j : ℕ) (m n : ℕ+) (c : Ioi (0 : ℕ)) :
    letI : NeZero c.val := ⟨c.property.ne'⟩
    spectralJHolomorphicCoefficient f (2*j+2)*
        gamma0PeterssonGramModulusTerm N b a (2*j+2) m n c =
      (gamma0TrueWidthKloostermanSum N b a c.val (n : ℤ) (m : ℤ)/
        (gamma0TrueWidthModulus N b a (c.val : ℝ) : ℂ))*
      spectralJOddSynthesisTerm f j
        (spectralPeterssonBesselArgument m n (gamma0TrueWidthModulus N b a (c.val : ℝ))) := by
  let _ : NeZero c.val := ⟨c.property.ne'⟩
  have hk : 2*j+2-1 = 2*j+1 := by omega
  calc
    _ = (gamma0TrueWidthKloostermanSum N b a c.val (n : ℤ) (m : ℤ)/
          (gamma0TrueWidthModulus N b a (c.val : ℝ) : ℂ))*
        (spectralJHolomorphicCoefficient f (2*j+2)*
          (2*(Real.pi : ℂ)*I^(-((2*j+2 : ℕ) : ℤ)))*
          Complex.besselJ ((2*j+1 : ℕ) : ℂ)
            (spectralPeterssonBesselArgument m n
              (gamma0TrueWidthModulus N b a (c.val : ℝ)) : ℂ)) := by
      dsimp only [gamma0PeterssonGramModulusTerm]
      rw [hk]
      ring
    _ = _ := by rw [spectralJHolomorphicCoefficient_odd_term]

theorem spectralJHolomorphicCoefficient_gram_modulus_summable (f : ℝ → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (N : ℕ) [NeZero N] (b a : SL(2, ℤ)) (m n : ℕ+) (c : Ioi (0 : ℕ)) :
    Summable (fun j : ℕ => ‖spectralJHolomorphicCoefficient f (2*j+2)*
        gamma0PeterssonGramModulusTerm N b a (2*j+2) m n c‖) := by
  simp_rw [spectralJHolomorphicCoefficient_gram_modulus,norm_mul]
  exact (spectralJOddSynthesis_summable_norm f hf hc hp _).mul_left _

theorem spectralJHolomorphicCoefficient_gram_modulus_sum (f : ℝ → ℂ)
    (N : ℕ) [NeZero N] (b a : SL(2, ℤ)) (m n : ℕ+) (c : Ioi (0 : ℕ)) :
    letI : NeZero c.val := ⟨c.property.ne'⟩
    (∑' j : ℕ, spectralJHolomorphicCoefficient f (2*j+2)*
        gamma0PeterssonGramModulusTerm N b a (2*j+2) m n c) =
      (gamma0TrueWidthKloostermanSum N b a c.val (n : ℤ) (m : ℤ)/
        (gamma0TrueWidthModulus N b a (c.val : ℝ) : ℂ))*
      spectralJOddSynthesis f
        (spectralPeterssonBesselArgument m n (gamma0TrueWidthModulus N b a (c.val : ℝ))) := by
  letI : NeZero c.val := ⟨c.property.ne'⟩
  simp_rw [spectralJHolomorphicCoefficient_gram_modulus]
  rw [tsum_mul_left]
  rfl

end ArtinMatthews
