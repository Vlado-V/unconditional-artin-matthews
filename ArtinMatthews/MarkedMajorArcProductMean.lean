module

public import ArtinMatthews.MarkedMajorArcProductPolynomial


set_option backward.privateInPublic true
@[expose] public section

/-! Actual translated-frequency mean-square bounds for the product of two
finite coefficient polynomials. The divisor reciprocal sum is retained so
its logarithmic loss is explicit. -/
namespace ArtinMatthews
open Finset OAI.TwoPointCorrelations MeasureTheory

lemma markedNaturalPolynomial_eq_mrt (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    markedNaturalPolynomial S a t =
      mrtExponentialPolynomial S a (fun n => Real.log (n:ℝ)) t := rfl

lemma markedNaturalPolynomial_continuous (S : Finset ℕ) (a : ℕ → ℂ) :
    Continuous (markedNaturalPolynomial S a) := by
  unfold markedNaturalPolynomial markedPrimePhase
  fun_prop

 theorem markedNaturalPolynomial_mean_square (S : Finset ℕ) {N : ℕ}
    (hS : S ⊆ Ioc 0 N) (a : ℕ → ℂ) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖markedNaturalPolynomial S a t‖^2) ≤
      8*Real.exp 1*(T+(N:ℝ))*∑ n ∈ S, ‖a n‖^2 := by
  have hrow : ∀ m ∈ S,
      (∑ n ∈ S, 2*T/(1+T^2*(Real.log (m:ℝ)-Real.log (n:ℝ))^2)) ≤ 8*(T+(N:ℝ)) := by
    intro m hm
    exact (sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => by positivity)).trans
      (mrt_logarithmic_kernel_row hT (hS hm))
  simp_rw [markedNaturalPolynomial_eq_mrt]
  calc
    _ ≤ Real.exp 1*∫ t : ℝ, Real.exp (-|t|/T)*
        ‖mrtExponentialPolynomial S a (fun n => Real.log (n:ℝ)) t‖^2 :=
      mrt_unweighted_mean_square_le _ _ _ hT
    _ ≤ Real.exp 1*(8*(T+(N:ℝ))*∑ n ∈ S, ‖a n‖^2) :=
      mul_le_mul_of_nonneg_left (mrt_weighted_mean_square_of_rows _ _ _ hT hrow)
        (Real.exp_pos _).le
    _ = _ := by ring

lemma markedNaturalPolynomial_translate (S : Finset ℕ) (a : ℕ → ℂ) (ξ t : ℝ) :
    markedNaturalPolynomial S a (t+ξ) =
      markedNaturalPolynomial S (fun n => a n*markedPrimePhase n ξ) t := by
  unfold markedNaturalPolynomial
  apply sum_congr rfl
  intro n _
  rw [markedPrimePhase_add]
  ring

 theorem markedNaturalPolynomial_translated_mean_square (S : Finset ℕ) {N : ℕ}
    (hS : S ⊆ Ioc 0 N) (a : ℕ → ℂ) (ξ : ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖markedNaturalPolynomial S a (t+ξ)‖^2) ≤
      8*Real.exp 1*(T+(N:ℝ))*∑ n ∈ S, ‖a n‖^2 := by
  simp_rw [markedNaturalPolynomial_translate]
  simpa only [norm_mul,markedPrimePhase_norm,mul_one] using
    markedNaturalPolynomial_mean_square S hS (fun n => a n*markedPrimePhase n ξ) hT

 theorem markedNaturalPolynomial_product_mean_square (S U : Finset ℕ) (a b : ℕ → ℂ)
    (N : ℕ) (A B ξ T : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : 0 < T)
    (hS : ∀ m ∈ S, 0 < m) (hU : ∀ n ∈ U, 0 < n)
    (hbound : ∀ m ∈ S, ∀ n ∈ U, m*n ≤ N)
    (ha : ∀ m ∈ S, ‖a m‖ ≤ A) (hb : ∀ n ∈ U, ‖b n‖ ≤ B) :
    (∫ t in -T..T,
      ‖markedNaturalPolynomial S a (t+ξ)*markedNaturalPolynomial U b (t+ξ)‖^2) ≤
      8*Real.exp 1*(T+(N:ℝ))*((A*B)^2*(N:ℝ)*(∑ d ∈ Icc 1 N,1/(d:ℝ))^3) := by
  simp_rw [markedNaturalPolynomial_product S U a b N hS hU hbound]
  have hh := markedNaturalPolynomial_translated_mean_square
    (S := Icc 1 N) (N := N) (fun n hn => mem_Ioc.mpr (mem_Icc.mp hn))
    (markedProductCoefficient S U a b) ξ hT
  exact hh.trans (mul_le_mul_of_nonneg_left
    (markedProductCoefficient_square_mass S U a b N A B hA hB ha hb) (by positivity))

end ArtinMatthews
