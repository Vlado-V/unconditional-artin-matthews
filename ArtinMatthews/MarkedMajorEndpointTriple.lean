module

public import ArtinMatthews.MarkedMajorMellinNormalization
public import ArtinMatthews.MarkedMajorArcProductPolynomial


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite endpoint factorization on literal positive integer triples. -/
namespace ArtinMatthews
open Finset

theorem markedMajorEndpointPolynomial_nat_phase (n : ℕ) (t : ℝ) :
    Complex.exp (Complex.I*(t:ℂ)*(Real.log (n:ℝ):ℂ)) = markedPrimePhase n t := by
  unfold markedPrimePhase
  congr 1
  push_cast
  ring

theorem markedMajorEndpointPolynomial_triple (S T R : Finset ℕ)
    (a b c : ℕ → ℂ) (hS : ∀ s ∈ S,0 < s) (hT : ∀ m ∈ T,0 < m)
    (hR : ∀ n ∈ R,0 < n) (t : ℝ) :
    markedMajorEndpointPolynomial (S×ˢ(T×ˢR))
      (fun z => a z.1*b z.2.1*c z.2.2)
      (fun z => ((z.1*z.2.1*z.2.2:ℕ):ℝ)) t =
      (∑ s ∈ S,a s*markedPrimePhase s t)*
      (∑ m ∈ T,b m*markedPrimePhase m t)*
      (∑ n ∈ R,c n*markedPrimePhase n t) := by
  unfold markedMajorEndpointPolynomial
  rw [sum_product]
  simp only [sum_product,markedMajorEndpointPolynomial_nat_phase]
  rw [sum_mul_sum]
  simp only [sum_mul]
  apply sum_congr rfl
  intro s hs
  apply sum_congr rfl
  intro m hm
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  rw [← markedPrimePhase_mul (Nat.mul_pos (hS s hs) (hT m hm)) (hR n hn),
    ← markedPrimePhase_mul (hS s hs) (hT m hm)]
  ring

end ArtinMatthews
