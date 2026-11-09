module

public import ArtinMatthews.SpectralJHolomorphicInfinitySum


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute convergence justifies the actual odd-weight/modulus interchange,
retaining the source Kloosterman order and true-width scaling. -/
noncomputable section
open Set Complex
open scoped MatrixGroups

namespace ArtinMatthews

theorem spectralJHolomorphicCoefficient_leftInfinity_interchange
    (f : ℝ → ℂ) (hf : Continuous f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) (N : ℕ) [NeZero N]
    (b : SL(2, ℤ)) (m n : ℕ+) :
    (∑' j : ℕ, ∑' c : Ioi (0 : ℕ), spectralJHolomorphicCoefficient f (2*j+2)*
        gamma0PeterssonGramModulusTerm N b 1 (2*j+2) m n c) =
      ∑' c : Ioi (0 : ℕ),
        letI : NeZero c.val := ⟨c.property.ne'⟩
        (gamma0TrueWidthKloostermanSum N b 1 c.val (n : ℤ) (m : ℤ)/
          (gamma0TrueWidthModulus N b 1 (c.val : ℝ) : ℂ))*
          spectralJOddSynthesis f (spectralPeterssonBesselArgument m n
            (gamma0TrueWidthModulus N b 1 (c.val : ℝ))) := by
  have hs := (spectralJHolomorphicCoefficient_leftInfinity_summable_norm f hf hc hp N b m n).of_norm
  calc
    _ = ∑' c : Ioi (0 : ℕ), ∑' j : ℕ, spectralJHolomorphicCoefficient f (2*j+2)*
        gamma0PeterssonGramModulusTerm N b 1 (2*j+2) m n c := hs.tsum_comm.symm
    _ = _ := tsum_congr fun c => spectralJHolomorphicCoefficient_gram_modulus_sum f N b 1 m n c

end ArtinMatthews
