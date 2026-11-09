module

public import ArtinMatthews.VaryingKummerAnalyticRayIdealEuler
public import ArtinMatthews.VaryingKummerAnalyticRayUnramifiedEuler


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite old-modulus Euler correction for a genuine primitive
ideal-conductor character. Every conductor-prime omission is retained. -/
namespace ArtinMatthews.VaryingKummerAnalytic
noncomputable section
open NumberField FractionalIdeal Set Module Filter Topology
open OAI.PrimeDegreePackets
open scoped BigOperators NumberField nonZeroDivisors Classical
namespace EvenIdealRayCharacter
open EvenRayCharacter (badPrimes)
variable {K : Type*} [Field K] [NumberField K] {f : Ideal (𝓞 K)}
variable (Ψ : EvenIdealRayCharacter K f)

def primeEulerCorrection (p : Nat.Primes) (s : ℂ) : ℂ :=
  ∏ P : idealsOverPrime K (p:ℕ),
    (1 - Ψ.allCoefficient P.val * (Ideal.absNorm P.val : ℂ)^(-s))

def rationalBadEulerCorrection (N : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ badPrimes N, primeEulerCorrection Ψ p s

lemma primeEulerCorrection_ne_zero
    (p : Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    primeEulerCorrection Ψ p s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro P _
  have hnorm : 1 < (Ideal.absNorm P.val : ℝ) := by
    exact_mod_cast idealsOverPrime_norm_two_le K P.property
  have H : ‖Ψ.allCoefficient P.val *
      (Ideal.absNorm P.val : ℂ)^(-s)‖ < 1 := by
    rw [norm_mul]
    have HN : ‖(Ideal.absNorm P.val : ℂ)^(-s)‖ < 1 := by
      have HN := Complex.norm_cpow_eq_rpow_re_of_pos
        (show 0 < (Ideal.absNorm P.val : ℝ) by linarith) (-s)
      simp only [Complex.ofReal_natCast, Complex.neg_re] at HN
      rw [HN]
      exact Real.rpow_lt_one_of_one_lt_of_neg hnorm (neg_neg_of_pos hs)
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (Ψ.allCoefficient_norm_le_one P.val)).trans_lt HN
  intro hz
  rw [← sub_eq_zero.mp hz, norm_one] at H
  exact (lt_irrefl _ H)

lemma rationalBadEulerCorrection_ne_zero
    (N : ℕ) {s : ℂ} (hs : 0 < s.re) : rationalBadEulerCorrection Ψ N s ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun p _ => primeEulerCorrection_ne_zero Ψ p hs)

lemma primeEulerCorrection_entire
    (p : Nat.Primes) : Differentiable ℂ (primeEulerCorrection Ψ p) := by
  apply Differentiable.fun_finsetProd
  intro P _
  apply Differentiable.const_sub
  apply Differentiable.const_mul
  apply Differentiable.const_cpow differentiable_neg
  exact Or.inl (by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2)
    (idealsOverPrime_norm_two_le K P.property)).ne')

lemma rationalBadEulerCorrection_entire
    (N : ℕ) : Differentiable ℂ (rationalBadEulerCorrection Ψ N) := by
  exact Differentiable.fun_finsetProd (fun p _ => primeEulerCorrection_entire Ψ p)

lemma primeEulerCorrection_inv
    (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    ∏ P : idealsOverPrime K (p:ℕ),
      (1 - Ψ.idealTerm hs P.val)⁻¹ =
        (primeEulerCorrection Ψ p s)⁻¹ := by
  rw [primeEulerCorrection, ← Finset.prod_inv_distrib]
  rfl

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
