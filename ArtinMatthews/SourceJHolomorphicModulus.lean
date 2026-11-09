module

public import ArtinMatthews.SpectralJHolomorphicInfinityInterchange
public import ArtinMatthews.SpectralPeterssonSourceGram
public import ArtinMatthews.SpectralABLOppositeModulus


set_option backward.privateInPublic true
@[expose] public section

/-! The odd J synthesis is the literal signed geometric contribution of
every even holomorphic weight, including weight two. -/
namespace ArtinMatthews
open Set
open scoped MatrixGroups ComplexConjugate
noncomputable section

def sourceJHolomorphicSignedIndex (negative : Bool) (n : ℕ+) : ℤ :=
  if negative then -(n : ℤ) else (n : ℤ)

theorem sourceJHolomorphicSignedIndex_ne_zero (negative : Bool) (n : ℕ+) :
    sourceJHolomorphicSignedIndex negative n ≠ 0 := by
  have hn : (n : ℤ) ≠ 0 := by exact_mod_cast n.property.ne'
  cases negative <;> simpa [sourceJHolomorphicSignedIndex] using hn

private theorem signed_argument (negative : Bool) (m n : ℕ+) (C : ℝ) :
    4*Real.pi*Real.sqrt
        (|(sourceJHolomorphicSignedIndex negative n : ℝ)*
          (sourceJHolomorphicSignedIndex negative m : ℝ)|)/C =
      spectralPeterssonBesselArgument m n C := by
  have hm : (0 : ℝ) ≤ m := by positivity
  have hn : (0 : ℝ) ≤ n := by positivity
  cases negative <;>
    simp [sourceJHolomorphicSignedIndex,spectralPeterssonBesselArgument,
      abs_of_nonneg (mul_nonneg hn hm),mul_comm]

private theorem signed_gram_formula (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k : ℕ) (negative : Bool) (m n : ℕ+) (c : Ioi (0 : ℕ)) :
    letI : NeZero c.val := ⟨c.property.ne'⟩
    gamma0PeterssonSignedGramModulusTerm N b a k negative m n c =
      gamma0TrueWidthKloostermanSum N b a c.val
          (sourceJHolomorphicSignedIndex negative n) (sourceJHolomorphicSignedIndex negative m)*
        (2*(Real.pi : ℂ)*Complex.I^(-(k : ℤ))/
          (gamma0TrueWidthModulus N b a (c.val : ℝ) : ℂ))*
        Complex.besselJ ((k-1 : ℕ) : ℂ)
          (spectralPeterssonBesselArgument m n (gamma0TrueWidthModulus N b a (c.val : ℝ)) : ℂ) := by
  cases negative <;> rfl

theorem sourceJHolomorphicSignedGram_norm (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k : ℕ) (hEven : Even k) (negative : Bool) (m n : ℕ+) (c : Ioi (0 : ℕ)) :
    ‖gamma0PeterssonSignedGramModulusTerm N b a k negative m n c‖ =
      ‖gamma0PeterssonGramModulusTerm N b a k m n c‖ := by
  cases negative
  · rfl
  · change ‖gamma0PeterssonNegativeGramModulusTerm N b a k m n c‖ = _
    rw [gamma0PeterssonNegativeGramModulusTerm_eq_conj N b a k hEven m n,Complex.norm_conj]

theorem sourceJHolomorphicCoefficient_signed_modulus (f : ℝ → ℂ)
    (N : ℕ) [NeZero N] (b a : SL(2, ℤ)) (j : ℕ) (negative : Bool)
    (m n : ℕ+) (c : Ioi (0 : ℕ)) :
    spectralJHolomorphicCoefficient f (2*j+2)*
        gamma0PeterssonSignedGramModulusTerm N b a (2*j+2) negative m n c =
      gamma0ABLOppositeGeometricTerm N b a c
        (sourceJHolomorphicSignedIndex negative n) (sourceJHolomorphicSignedIndex negative m)
        (spectralJOddSynthesisTerm f j) := by
  letI : NeZero c.val := ⟨c.property.ne'⟩
  have hk : 2*j+2-1 = 2*j+1 := by omega
  rw [signed_gram_formula]
  dsimp only [gamma0ABLOppositeGeometricTerm]
  rw [signed_argument negative m n]
  rw [hk]
  calc
    _ = (gamma0TrueWidthKloostermanSum N b a c.val
        (sourceJHolomorphicSignedIndex negative n) (sourceJHolomorphicSignedIndex negative m)/
        (gamma0TrueWidthModulus N b a (c.val : ℝ) : ℂ))*
      (spectralJHolomorphicCoefficient f (2*j+2)*
        (2*(Real.pi : ℂ)*Complex.I^(-((2*j+2 : ℕ) : ℤ)))*
        Complex.besselJ ((2*j+1 : ℕ) : ℂ)
          (spectralPeterssonBesselArgument m n (gamma0TrueWidthModulus N b a (c.val : ℝ)) : ℂ)) := by ring
    _ = _ := by rw [spectralJHolomorphicCoefficient_odd_term]

theorem sourceJHolomorphicCoefficient_signed_modulus_sum (f : ℝ → ℂ)
    (N : ℕ) [NeZero N] (b a : SL(2, ℤ)) (negative : Bool)
    (m n : ℕ+) (c : Ioi (0 : ℕ)) :
    (∑' j : ℕ, spectralJHolomorphicCoefficient f (2*j+2)*
        gamma0PeterssonSignedGramModulusTerm N b a (2*j+2) negative m n c) =
      gamma0ABLOppositeGeometricTerm N b a c
        (sourceJHolomorphicSignedIndex negative n) (sourceJHolomorphicSignedIndex negative m)
        (spectralJOddSynthesis f) := by
  simp_rw [sourceJHolomorphicCoefficient_signed_modulus]
  dsimp only [gamma0ABLOppositeGeometricTerm]
  rw [tsum_mul_left]
  rfl

theorem sourceJHolomorphicCoefficient_signed_joint_summable (f : ℝ → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (N : ℕ) [NeZero N] (b : SL(2, ℤ)) (negative : Bool) (m n : ℕ+) :
    Summable (fun p : ℕ × Ioi (0 : ℕ) => ‖spectralJHolomorphicCoefficient f (2*p.1+2)*
      gamma0PeterssonSignedGramModulusTerm N b 1 (2*p.1+2) negative m n p.2‖) := by
  have he (j : ℕ) : Even (2*j+2) := ⟨j+1,by omega⟩
  simpa only [norm_mul,sourceJHolomorphicSignedGram_norm N b 1 _ (he _) negative m n] using
    spectralJHolomorphicCoefficient_leftInfinity_summable_norm f hf hc hp N b m n

end
end ArtinMatthews
