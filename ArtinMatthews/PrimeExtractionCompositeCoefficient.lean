module

public import ArtinMatthews.PrimeExtractionSquarefreeIdentity


set_option backward.privateInPublic true
@[expose] public section

/-! Exact coefficient expansion after partitioning rough squarefree
composites by their number of prime factors. -/

namespace ArtinMatthews

open OAI.SevenEighths
open scoped BigOperators

theorem roughPrimeTupleCoefficient_eq_zero_of_length_ne (a : ℕ → ℂ) (j n : ℕ) (z : ℝ)
    (hne : n.primeFactorsList.length ≠ j) : roughPrimeTupleCoefficient a j n z = 0 := by
  by_contra h
  exact hne (roughPrimeTupleCoefficient_support a j n z h).2.2

noncomputable def roughCompositeCoefficient (a : ℕ → ℂ) (J n : ℕ) (z : ℝ) : ℂ :=
  ∑ j ∈ Finset.Icc 2 J, roughPrimeTupleCoefficient a j n z / j.factorial

theorem roughCompositeCoefficient_squarefree (a : ArithmeticFunction ℂ)
    (ha : a.IsMultiplicative) (J : ℕ) {n : ℕ} (hn : Squarefree n) {z : ℝ}
    (hrough : MarkedRoughAbove z n) :
    roughCompositeCoefficient a J n z =
      if n.primeFactorsList.length ∈ Finset.Icc 2 J then a n else 0 := by
  classical
  unfold roughCompositeCoefficient
  by_cases hlen : n.primeFactorsList.length ∈ Finset.Icc 2 J
  · rw [ite_eq_left hlen, Finset.sum_eq_single n.primeFactorsList.length]
    · rw [squarefree_roughPrimeTupleCoefficient a ha hn hrough rfl]
      have hfac : (n.primeFactorsList.length.factorial : ℂ) ≠ 0 :=
        by exact_mod_cast Nat.factorial_ne_zero _
      field_simp
    · intro j _ hj
      rw [roughPrimeTupleCoefficient_eq_zero_of_length_ne a j n z hj.symm, zero_div]
    · exact fun h => (h hlen).elim
  · rw [ite_eq_right hlen]
    apply Finset.sum_eq_zero
    intro j hj
    have hne : n.primeFactorsList.length ≠ j := fun h => hlen (h ▸ hj)
    rw [roughPrimeTupleCoefficient_eq_zero_of_length_ne a j n z hne, zero_div]

theorem primeFactorsList_length_ge_two_iff {n : ℕ} (hn : n ≠ 0) :
    2 ≤ n.primeFactorsList.length ↔ n ≠ 1 ∧ ¬n.Prime := by
  have hz : n.primeFactorsList.length = 0 ↔ n = 0 ∨ n = 1 := by
    simpa only [ArithmeticFunction.cardFactors_apply] using
      (ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one (n := n))
  have ho : n.primeFactorsList.length = 1 ↔ n.Prime := by
    simpa only [ArithmeticFunction.cardFactors_apply] using
      (ArithmeticFunction.cardFactors_eq_one_iff_prime (n := n))
  constructor
  · intro h
    constructor
    · intro hn1
      have := hz.mpr (Or.inr hn1)
      omega
    · intro hp
      have := ho.mpr hp
      omega
  · rintro ⟨hn1, hnp⟩
    have hne0 : n.primeFactorsList.length ≠ 0 := fun h => (hz.mp h).elim hn hn1
    have hne1 : n.primeFactorsList.length ≠ 1 := fun h => hnp (ho.mp h)
    omega

/-- A squarefree rough composite is represented by the finite factorial
sum with the actual theta coefficient, while a prime or 1 contributes zero. -/
theorem roughThetaCompositeCoefficient_eq (η : HeckeFamily.Character)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (J : ℕ) {n : ℕ} (hn : Squarefree n) {z : ℝ}
    (hrough : MarkedRoughAbove z n) (hJ : n.primeFactorsList.length ≤ J) :
    roughCompositeCoefficient (fun p => idealThetaCoeff η p * χ p) J n z =
      if n ≠ 1 ∧ ¬n.Prime then idealThetaCoeff η n * χ n else 0 := by
  have h := roughCompositeCoefficient_squarefree (twistedThetaArithmeticFunction η χ)
    (twistedThetaArithmeticFunction_isMultiplicative η χ) J hn hrough
  change roughCompositeCoefficient (fun p => idealThetaCoeff η p * χ p) J n z =
    (if n.primeFactorsList.length ∈ Finset.Icc 2 J then idealThetaCoeff η n * χ n else 0) at h
  simpa only [Finset.mem_Icc, and_iff_left hJ,
    primeFactorsList_length_ge_two_iff hn.ne_zero] using h

end ArtinMatthews
