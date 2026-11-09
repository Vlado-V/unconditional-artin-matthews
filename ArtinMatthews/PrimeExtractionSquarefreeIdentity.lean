module

public import ArtinMatthews.PrimeExtractionTupleBounds
public import ArtinMatthews.CubicThetaCoefficientMultiplicative


set_option backward.privateInPublic true
@[expose] public section

/-! Exact factorial expansion for the genuine squarefree theta coefficient.
The coprime multiplicativity input is discharged by the ideal-norm fiber theorem. -/

namespace ArtinMatthews

open OAI.SevenEighths
open scoped BigOperators

noncomputable def twistedThetaArithmeticFunction (η : HeckeFamily.Character)
    {q : ℕ} (χ : DirichletCharacter ℂ q) : ArithmeticFunction ℂ where
  toFun n := idealThetaCoeff η n * χ n
  map_zero' := by simp

theorem twistedThetaArithmeticFunction_isMultiplicative (η : HeckeFamily.Character)
    {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (twistedThetaArithmeticFunction η χ).IsMultiplicative := by
  constructor
  · simp [twistedThetaArithmeticFunction]
  · intro m n hmn
    change idealThetaCoeff η (m * n) * χ ((m * n : ℕ) : ZMod q) = _
    rw [idealThetaCoeff_mul_of_coprime η hmn, Nat.cast_mul, map_mul]
    change _ = (idealThetaCoeff η m * χ m) * (idealThetaCoeff η n * χ n)
    ring

theorem squarefree_ordered_coefficient_product (a : ArithmeticFunction ℂ)
    (ha : a.IsMultiplicative) {n : ℕ} (hn : Squarefree n)
    {l : List ℕ} (hl : l ∈ orderedPrimeFactorizations n) : (l.map a).prod = a n := by
  have hperm := List.mem_permutations.mp (List.mem_toFinset.mp hl)
  calc
    _ = (n.primeFactorsList.map a).prod := (hperm.map a).prod_eq
    _ = ∏ p ∈ n.primeFactors, a p := by
      simpa only [Nat.toFinset_factors] using
        (List.prod_toFinset a ((Nat.squarefree_iff_nodup_primeFactorsList hn.ne_zero).mp hn)).symm
    _ = a n := ha.prod_primeFactors hn

/-- Every squarefree rough integer with j prime factors occurs exactly j!
times, and every ordered tuple has its genuine coefficient a(n). -/
theorem squarefree_roughPrimeTupleCoefficient (a : ArithmeticFunction ℂ)
    (ha : a.IsMultiplicative) {j n : ℕ} (hn : Squarefree n) {z : ℝ}
    (hrough : MarkedRoughAbove z n) (hj : n.primeFactorsList.length = j) :
    roughPrimeTupleCoefficient a j n z = (j.factorial : ℂ) * a n := by
  unfold roughPrimeTupleCoefficient
  rw [roughOrderedPrimeFactorizations_eq hn.ne_zero hrough hj]
  calc
    _ = ∑ _l ∈ orderedPrimeFactorizations n, a n :=
      Finset.sum_congr rfl (fun _ hl => squarefree_ordered_coefficient_product a ha hn hl)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, orderedPrimeFactorizations_card hn, hj]

/-- The arithmetic factorial identity needed in Proposition 8.1, for the
actual ideal-theta coefficient times any Dirichlet character. -/
theorem squarefree_theta_ordered_factorization (η : HeckeFamily.Character)
    {q : ℕ} (χ : DirichletCharacter ℂ q) {j n : ℕ} (hn : Squarefree n) {z : ℝ}
    (hrough : MarkedRoughAbove z n) (hj : n.primeFactorsList.length = j) :
    idealThetaCoeff η n * χ n =
      roughPrimeTupleCoefficient (fun p => idealThetaCoeff η p * χ p) j n z / j.factorial := by
  have h := squarefree_roughPrimeTupleCoefficient (twistedThetaArithmeticFunction η χ)
    (twistedThetaArithmeticFunction_isMultiplicative η χ) hn hrough hj
  change roughPrimeTupleCoefficient (fun p => idealThetaCoeff η p * χ p) j n z =
    (j.factorial : ℂ) * (idealThetaCoeff η n * χ n) at h
  rw [h]
  have hfac : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  field_simp

end ArtinMatthews
