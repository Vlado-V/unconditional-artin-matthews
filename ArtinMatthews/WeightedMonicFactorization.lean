module

public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Basic.Complex.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Finite normalized-factor identities for monic polynomials. These use
unique factorization only and contain no character or Gauss-sum premise. -/
namespace ArtinMatthews.WeightedMonic
noncomputable section
open Polynomial UniqueFactorizationMonoid
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F]

def exponent (P Q : F[X]) : ℕ := (normalizedFactors Q).count P

theorem factors_product {Q : F[X]} (hQ : Q.Monic) : (normalizedFactors Q).prod = Q :=
  (prod_normalizedFactors_eq hQ.ne_zero).trans hQ.normalize_eq_self

theorem factor_spec {Q P : F[X]} (hQ : Q.Monic) (hP : P ∈ normalizedFactors Q) :
    Irreducible P ∧ P.Monic ∧ P ∣ Q :=
  (Polynomial.mem_normalizedFactors_iff hQ.ne_zero).mp hP

theorem power_dvd_iff_exponent {P Q : F[X]} (hP : P.Monic) (hi : Irreducible P)
    (hQ : Q ≠ 0) (r : ℕ) : P^r ∣ Q ↔ r ≤ exponent P Q := by
  rw [dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero _ hi.ne_zero) hQ,
    hi.normalizedFactors_pow,hP.normalize_eq_self,← Multiset.le_count_iff_replicate_le]
  rfl

theorem degree_eq_factor_sum {Q : F[X]} (hQ : Q.Monic) :
    Q.natDegree = ∑ P ∈ (normalizedFactors Q).toFinset, exponent P Q * P.natDegree := by
  calc
    Q.natDegree = (normalizedFactors Q).prod.natDegree := congrArg natDegree (factors_product hQ).symm
    _ = ((normalizedFactors Q).map natDegree).sum :=
      natDegree_multiset_prod_of_monic _ (fun P hP => (factor_spec hQ hP).2.1)
    _ = _ := by simpa only [exponent,smul_eq_mul] using Finset.sum_multiset_map_count (normalizedFactors Q) natDegree

theorem exponent_mul_degree_le {P Q : F[X]} (hP : P.Monic) (hi : Irreducible P) (hQ : Q.Monic) :
    exponent P Q * P.natDegree ≤ Q.natDegree := by
  have hd : P^(exponent P Q) ∣ Q := (power_dvd_iff_exponent hP hi hQ.ne_zero _).mpr le_rfl
  simpa only [natDegree_pow] using natDegree_le_of_dvd hd hQ.ne_zero

theorem exponent_le_degree {P Q : F[X]} (hP : P.Monic) (hi : Irreducible P) (hQ : Q.Monic) :
    exponent P Q ≤ Q.natDegree := by
  have hp := hi.natDegree_pos
  have hd := exponent_mul_degree_le hP hi hQ
  nlinarith

theorem monic_weight_pow (w : F[X] → ℂ) (h1 : w 1 = 1)
    (hm : ∀ P Q, P.Monic → Q.Monic → w (P*Q) = w P*w Q)
    {P : F[X]} (hP : P.Monic) (r : ℕ) : w (P^r) = w P^r := by
  induction r with
  | zero => simpa only [pow_zero] using h1
  | succ r ih => rw [pow_succ,hm _ _ (hP.pow r) hP,ih,pow_succ]

end
end ArtinMatthews.WeightedMonic
