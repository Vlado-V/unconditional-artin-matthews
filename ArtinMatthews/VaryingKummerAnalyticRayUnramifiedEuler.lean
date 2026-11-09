module

public import ArtinMatthews.VaryingKummerAnalyticRayUnramifiedAlgebra


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine finite conductor-prime deletion for residue-one ray series.
The generic local Euler proof is extracted unchanged from RayUnramified. -/

namespace ArtinMatthews.VaryingKummerAnalytic
noncomputable section
open NumberField FractionalIdeal Set Module Filter Topology
open OAI.PrimeDegreePackets
open scoped BigOperators NumberField nonZeroDivisors Classical
namespace EvenRayCharacter
variable {K : Type*} [Field K] [NumberField K] {N : ℕ}
variable (ψ : EvenRayCharacter K N)

lemma classRay_allCoefficient (χ : ClassGroup (𝓞 K) →* ℂˣ)
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    (classRayCharacter χ).allCoefficient I =
      (χ (ClassGroup.mk K (integralIdealFractionalUnit I hI)) : ℂ) := by
  simp only [allCoefficient, dite_eq_left hI, coprime_modulus_one, ite_true,
    classRayCharacter, MonoidHom.comp_apply]

 
def badPrimes (N : ℕ) : Finset Nat.Primes := N.primeFactors.subtype Nat.Prime

lemma mem_badPrimes [NeZero N] (p : Nat.Primes) :
    p ∈ badPrimes N ↔ (p : ℕ) ∣ N := by
  change (⟨p.val, p.property⟩ : {p : ℕ // p.Prime}) ∈
    N.primeFactors.subtype Nat.Prime ↔ _
  simp only [Finset.mem_subtype, Nat.mem_primeFactors,
    p.property, true_and]
  exact and_iff_left (NeZero.ne N)

 
def classEulerCorrection (χ : ClassGroup (𝓞 K) →* ℂˣ) (p : Nat.Primes) (s : ℂ) : ℂ :=
  ∏ P : idealsOverPrime K (p:ℕ),
    (1 - (classRayCharacter χ).allCoefficient P.val * (Ideal.absNorm P.val : ℂ)^(-s))

def badEulerCorrection (χ : ClassGroup (𝓞 K) →* ℂˣ) (N : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ badPrimes N, classEulerCorrection χ p s

lemma classEulerCorrection_ne_zero (χ : ClassGroup (𝓞 K) →* ℂˣ)
    (p : Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    classEulerCorrection χ p s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro P _
  have hnorm : 1 < (Ideal.absNorm P.val : ℝ) := by
    exact_mod_cast idealsOverPrime_norm_two_le K P.property
  have H : ‖(classRayCharacter χ).allCoefficient P.val *
      (Ideal.absNorm P.val : ℂ)^(-s)‖ < 1 := by
    rw [norm_mul]
    have HN : ‖(Ideal.absNorm P.val : ℂ)^(-s)‖ < 1 := by
      have HN := Complex.norm_cpow_eq_rpow_re_of_pos
        (show 0 < (Ideal.absNorm P.val : ℝ) by linarith) (-s)
      simp only [Complex.ofReal_natCast, Complex.neg_re] at HN
      rw [HN]
      exact Real.rpow_lt_one_of_one_lt_of_neg hnorm (neg_neg_of_pos hs)
    exact (mul_le_of_le_one_left (norm_nonneg _)
      ((classRayCharacter χ).allCoefficient_norm_le_one P.val)).trans_lt HN
  intro hz
  rw [← sub_eq_zero.mp hz, norm_one] at H
  exact (lt_irrefl _ H)

lemma badEulerCorrection_ne_zero (χ : ClassGroup (𝓞 K) →* ℂˣ)
    (N : ℕ) {s : ℂ} (hs : 0 < s.re) : badEulerCorrection χ N s ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun p _ => classEulerCorrection_ne_zero χ p hs)

lemma classEulerCorrection_entire (χ : ClassGroup (𝓞 K) →* ℂˣ)
    (p : Nat.Primes) : Differentiable ℂ (classEulerCorrection χ p) := by
  apply Differentiable.fun_finsetProd
  intro P _
  apply Differentiable.const_sub
  apply Differentiable.const_mul
  apply Differentiable.const_cpow differentiable_neg
  exact Or.inl (by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2)
    (idealsOverPrime_norm_two_le K P.property)).ne')

lemma badEulerCorrection_entire (χ : ClassGroup (𝓞 K) →* ℂˣ)
    (N : ℕ) : Differentiable ℂ (badEulerCorrection χ N) := by
  exact Differentiable.fun_finsetProd (fun p _ => classEulerCorrection_entire χ p)

lemma classEulerCorrection_inv (χ : ClassGroup (𝓞 K) →* ℂˣ)
    (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    ∏ P : idealsOverPrime K (p:ℕ),
      (1 - (classRayCharacter χ).idealTerm hs P.val)⁻¹ =
        (classEulerCorrection χ p s)⁻¹ := by
  rw [classEulerCorrection, ← Finset.prod_inv_distrib]
  rfl

variable [NeZero N]

lemma local_euler_of_residue_one (hψ : ψ.residue = 1)
    (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    (∏ P : idealsOverPrime K (p:ℕ), (1 - ψ.idealTerm hs P.val)⁻¹) =
      (classEulerCorrection (ψ.classUnitCharacter hψ) p s)⁻¹ *
        (if p ∈ badPrimes N then classEulerCorrection (ψ.classUnitCharacter hψ) p s else 1) := by
  by_cases hb : p ∈ badPrimes N
  · rw [ite_eq_left hb, inv_mul_cancel₀ (classEulerCorrection_ne_zero _ p (by linarith))]
    apply Finset.prod_eq_one
    intro P _
    have hc : ¬ IsCoprime P.val (rationalModulusIdeal (𝓞 K) N) := by
      rw [coprime_idealOverPrime_iff p.property P]
      exact not_not.mpr ((mem_badPrimes p).mp hb)
    have hp0 : P.val ≠ ⊥ := (idealsOverPrime_prime K P.property).ne_zero
    simp only [idealTerm_apply, allCoefficient, dite_eq_left hp0, hc, ite_false,
      zero_mul, sub_zero, inv_one]
  · rw [ite_eq_right hb, mul_one, ← classEulerCorrection_inv _ p hs]
    apply Finset.prod_congr rfl
    intro P _
    have hc : IsCoprime P.val (rationalModulusIdeal (𝓞 K) N) := by
      rw [coprime_idealOverPrime_iff p.property P]
      exact (mem_badPrimes p).not.mp hb
    have hp0 : P.val ≠ ⊥ := (idealsOverPrime_prime K P.property).ne_zero
    congr 2
    rw [idealTerm_apply, idealTerm_apply, classRay_allCoefficient _ hp0,
      allCoefficient_of_residue_one ψ hψ _ hp0, ite_eq_left hc]
    rfl

 

theorem dirichlet_of_residue_one (hψ : ψ.residue = 1)
    {s : ℂ} (hs : 1 < s.re) :
    ψ.dirichlet s = idealClassDirichlet K (ψ.classCharacter hψ) s *
      badEulerCorrection (ψ.classUnitCharacter hψ) N s := by
  let χ := ψ.classUnitCharacter hψ
  have HF := (classRayCharacter χ).dirichlet_hasProd hs
  simp_rw [classEulerCorrection_inv χ _ hs] at HF
  have HB : HasProd (fun p : Nat.Primes =>
      if p ∈ badPrimes N then classEulerCorrection χ p s else 1)
      (badEulerCorrection χ N s) := by
    have HT := hasProd_prod_of_ne_finset_one (s := badPrimes N)
      (f := fun p : Nat.Primes => if p ∈ badPrimes N then classEulerCorrection χ p s else 1)
      (L := SummationFilter.unconditional _) (fun p hp => ite_eq_right hp)
    simpa only [badEulerCorrection, Finset.prod_ite_mem, Finset.inter_self] using HT
  have H := HF.mul HB
  have HR := ψ.dirichlet_hasProd hs
  simp_rw [ψ.local_euler_of_residue_one hψ _ hs] at HR
  have HE := HR.unique H
  rw [classRay_dirichlet χ s] at HE
  exact HE

 


end EvenRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic

