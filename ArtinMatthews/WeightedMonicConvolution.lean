module

public import ArtinMatthews.WeightedMonicPointing
public import ArtinMatthews.WeightedMonicDivisorSum
public import ArtinMatthews.WeightedMonicPointedSum


set_option backward.privateInPublic true
@[expose] public section

/-! The degree-weighted monic coefficient is a finite sum over extracted
irreducible powers and their monic quotients. Every factorization and
quotient map used here is proved, not an Euler-product premise. -/
namespace ArtinMatthews.WeightedMonic
noncomputable section
open Polynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F]

theorem power_divisor_weight_sum (w : F[X] → ℂ) (h1 : w 1=1)
    (hm : ∀ P Q,P.Monic → Q.Monic → w (P*Q)=w P*w Q)
    {P : F[X]} (hP : P.Monic) (n r : ℕ) :
    (∑ Q ∈ layer n,if P^r ∣ Q then w Q else 0) =
      if r*P.natDegree ≤ n then w P^r*coefficient w (n-r*P.natDegree) else 0 := by
  by_cases hr : r*P.natDegree ≤ n
  · let p : MonicDegreeEq F (r*P.natDegree) := MonicDegreeEq.mk (P^r) (hP.pow r) (natDegree_pow P r)
    have hs := divisor_weight_sum w hm p hr
    change (∑ Q ∈ layer n,if P^r ∣ Q then w Q else 0) = w (P^r)*coefficient w (n-r*P.natDegree) at hs
    rw [monic_weight_pow w h1 hm hP r] at hs
    simpa only [ite_eq_left hr] using hs
  · rw [ite_eq_right hr]
    apply Finset.sum_eq_zero
    intro Q hQ
    have hd : ¬P^r ∣ Q := by
      intro hdiv
      obtain ⟨hq,hdeg⟩ := (mem_layer n Q).mp hQ
      have hh := natDegree_le_of_dvd hdiv hq.ne_zero
      rw [natDegree_pow,hdeg] at hh
      exact hr hh
    exact ite_eq_right hd

theorem coefficient_primePower_convolution (w : F[X] → ℂ) (h1 : w 1=1)
    (hm : ∀ P Q,P.Monic → Q.Monic → w (P*Q)=w P*w Q) (n : ℕ) :
    (n:ℂ)*coefficient w n =
      ∑ P ∈ atoms n, ∑ r ∈ Finset.Icc 1 n,
        if r*P.natDegree ≤ n then (P.natDegree:ℂ)*w P^r*coefficient w (n-r*P.natDegree) else 0 := by
  rw [coefficient_pointed_sum]
  apply Finset.sum_congr rfl
  intro P hP
  apply Finset.sum_congr rfl
  intro r _
  rw [power_divisor_weight_sum w h1 hm ((mem_atoms n P).mp hP).1]
  simp only [mul_ite,mul_zero,mul_assoc]

end
end ArtinMatthews.WeightedMonic
