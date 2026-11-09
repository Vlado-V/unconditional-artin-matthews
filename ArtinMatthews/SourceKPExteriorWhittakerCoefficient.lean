module

public import ArtinMatthews.SourceKPExteriorWhittakerPhase


set_option backward.privateInPublic true
@[expose] public section

/-! The literal exterior product for the actual local Whittaker
functions on the tame spherical cyclic representations. The CRT
phase and the two prime norm powers are combined on the same
finite set of primes. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic StandardAdelic QuadraticWeil
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)

local notation "D" => SourcePrimeExponents K S₀

private theorem sourceJacquetScale_neg_nat (Q : ℝ) (hQ : 0 ≤ Q) (k : ℕ) :
    sourceJacquetScale Q (-(k : ℝ)) = ((Q : ℂ) ^ k)⁻¹ := by
  rw [sourceJacquetScale, Real.rpow_neg hQ, Real.rpow_natCast, Complex.ofReal_inv, Complex.ofReal_pow]

theorem sourceKPTameCyclicWhittakerValue_diagonal_squarefree_cube
    (c : ReflectionSquarefreeExponents K S₀) (n : D) (P : SourceExteriorPrime K S₀) :
    sourceKPTameCyclicWhittakerValue K hζ S₀ P hS
      (sourceFiniteKP2ProjectiveLift K hζ P.val
        (sourceGL2Diagonal ((sourceKPTameExteriorUniformizer K hζ S₀ P) ^ ((c.val P + 3 * n P : ℕ) : ℤ)))) =
      reflectionNormalizedPrimeGamma K hζ S₀ P ^ c.val P /
        ((Real.sqrt (Ideal.absNorm P.val.asIdeal : ℝ) : ℂ) ^ c.val P * (Ideal.absNorm P.val.asIdeal : ℂ) ^ n P) := by
  let Q : ℝ := Ideal.absNorm P.val.asIdeal
  have hQ : 0 < Q := sourceJacquetPrimeNorm_pos K S₀ P
  have hcp : c.val P = 0 ∨ c.val P = 1 := by have h := c.property P; omega
  rcases hcp with h0 | h1
  · rw [h0, zero_add, pow_zero, pow_zero, one_mul, one_div,
      sourceKPTameCyclicWhittakerValue_diagonal_three, sourceJacquetScale_neg_nat Q hQ.le,
      Complex.ofReal_natCast]
  · rw [h1, pow_one, pow_one, add_comm 1,
      sourceKPTameCyclicWhittakerValue_diagonal_three_add_one, sourceJacquetActualGauss_two_eq_gamma,
      sub_eq_add_neg, show -(1 / 2 : ℝ) = -1 / 2 by ring,
      sourceJacquetScale_add hQ, sourceJacquetScale_neg_nat Q hQ.le,
      sourceJacquetScale_neg_half hQ.le, Complex.ofReal_natCast, div_eq_mul_inv, mul_inv_rev]
    ring

theorem sourceKPTameExteriorWhittakerDiagonal_squarefree_cube
    (c : ReflectionSquarefreeExponents K S₀) (n : D)
    (T : Finset (SourceExteriorPrime K S₀)) (hT : (c.val + 3 • n).support ⊆ T) (P : SourceExteriorPrime K S₀) :
    sourceKPTameExteriorWhittakerDiagonal K hζ S₀ P hS (sourcePrimeExponentUnit K hζ S₀ (c.val + 3 • n)) =
      ((∏ Q ∈ T, reflectionGaussPairKernel K hζ S₀ c P Q) * reflectionNormalizedPrimeGamma K hζ S₀ P ^ c.val P) /
        ((Real.sqrt (Ideal.absNorm P.val.asIdeal : ℝ) : ℂ) ^ c.val P * (Ideal.absNorm P.val.asIdeal : ℂ) ^ n P) := by
  rw [sourceKPTameExteriorWhittakerDiagonal_exponent,
    sourceKPExteriorWhittakerPhase_squarefree_cube K hζ S₀ P c n T hT]
  have he : (c.val + 3 • n) P = c.val P + 3 * n P := by
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [he, sourceKPTameCyclicWhittakerValue_diagonal_squarefree_cube K hζ S₀ hS c n P, mul_div_assoc]

theorem sourcePrimeExponentNorm_prefix (e : D) (T : Finset (SourceExteriorPrime K S₀))
    (hT : e.support ⊆ T) : sourcePrimeExponentNorm K S₀ e = ∏ P ∈ T, Ideal.absNorm P.val.asIdeal ^ e P := by
  unfold sourcePrimeExponentNorm Finsupp.prod
  apply Finset.prod_subset hT
  intro P _ hP
  rw [Finsupp.notMem_support_iff.mp hP]
  exact pow_zero _

private theorem sourceSquarefreeNormSqrt_prefix (c : ReflectionSquarefreeExponents K S₀)
    (T : Finset (SourceExteriorPrime K S₀)) (hT : c.val.support ⊆ T) :
    (Real.sqrt (sourcePrimeExponentNorm K S₀ c.val : ℝ) : ℂ) =
      ∏ P ∈ T, (Real.sqrt (Ideal.absNorm P.val.asIdeal : ℝ) : ℂ) ^ c.val P := by
  rw [reflectionSquarefreeNorm_sqrt_support, Complex.ofReal_prod]
  have he : (∏ P : c.val.support, (Real.sqrt (Ideal.absNorm P.val.val.asIdeal : ℝ) : ℂ)) =
      ∏ P ∈ c.val.support, (Real.sqrt (Ideal.absNorm P.val.asIdeal : ℝ) : ℂ) :=
    Finset.prod_coe_sort c.val.support
      (fun P : SourceExteriorPrime K S₀ => (Real.sqrt (Ideal.absNorm P.val.asIdeal : ℝ) : ℂ))
  rw [he]
  calc
    _ = ∏ P ∈ c.val.support, (Real.sqrt (Ideal.absNorm P.val.asIdeal : ℝ) : ℂ) ^ c.val P := by
      apply Finset.prod_congr rfl
      intro P hP
      rw [reflectionSquarefreeExponent_support_one K S₀ c ⟨P, hP⟩, pow_one]
    _ = _ := by
      apply Finset.prod_subset hT
      intro P _ hP
      rw [Finsupp.notMem_support_iff.mp hP, pow_zero]

theorem sourceKPTameExteriorWhittakerProduct_squarefree_cube
    (c : ReflectionSquarefreeExponents K S₀) (n : D)
    (T : Finset (SourceExteriorPrime K S₀)) (hc : c.val.support ⊆ T) (hn : n.support ⊆ T) :
    (∏ P ∈ T, sourceKPTameExteriorWhittakerDiagonal K hζ S₀ P hS
        (sourcePrimeExponentUnit K hζ S₀ (c.val + 3 • n))) =
      reflectionGammaTwo K hζ S₀ c.val /
        ((Real.sqrt (sourcePrimeExponentNorm K S₀ c.val : ℝ) : ℂ) * (sourcePrimeExponentNorm K S₀ n : ℂ)) := by
  have hT : (c.val + 3 • n).support ⊆ T := by
    intro P hP
    by_contra h
    have hc0 : c.val P = 0 := Finsupp.notMem_support_iff.mp (fun h' => h (hc h'))
    have hn0 : n P = 0 := Finsupp.notMem_support_iff.mp (fun h' => h (hn h'))
    exact (Finsupp.mem_support_iff.mp hP) (by
      simp only [Finsupp.add_apply, Finsupp.smul_apply, hc0, hn0, smul_zero, add_zero])
  simp_rw [sourceKPTameExteriorWhittakerDiagonal_squarefree_cube K hζ S₀ hS c n T hT]
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    ← reflectionGammaTwo_eq_prefix K hζ S₀ c T hc, ← sourceSquarefreeNormSqrt_prefix K S₀ c T hc,
    sourcePrimeExponentNorm_prefix K S₀ n T hn, Nat.cast_prod]
  simp only [Nat.cast_pow]

end
end ArtinMatthews
