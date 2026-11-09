module

public import ArtinMatthews.MarkedSparsePrimeMoments
public import ArtinMatthews.MarkedSparsePhaseHarmonic


set_option backward.privateInPublic true
@[expose] public section

/-! Literal dyadic integer kernels and polynomial samples for the sparse
frequency argument. The normalization and coefficient vector are retained. -/

namespace ArtinMatthews

open scoped BigOperators ComplexConjugate
open OAI.TwoPointCorrelations

noncomputable section

def markedLogKernel (L R : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc L R, markedPrimePhase n t

def markedDyadicPolynomial (L R : ℕ) (H : ℝ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  (∑ n ∈ Finset.Icc L R, a n * markedPrimePhase n t) / H

theorem markedLogKernel_eq_mrt (L R : ℕ) (t : ℝ) :
    markedLogKernel L R t =
      mrtExponentialPolynomial (Finset.Icc L R) (fun _ => 1)
        (fun n => Real.log (n : ℝ)) t := by
  simp only [markedLogKernel, mrtExponentialPolynomial, one_mul, markedPrimePhase]

theorem markedDyadicPolynomial_eq_mrt (L R : ℕ) (H : ℝ)
    (a : ℕ → ℂ) (t : ℝ) :
    markedDyadicPolynomial L R H a t =
      mrtExponentialPolynomial (Finset.Icc L R) (fun n => a n / H)
        (fun n => Real.log (n : ℝ)) t := by
  unfold markedDyadicPolynomial mrtExponentialPolynomial
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _
  dsimp only [markedPrimePhase]
  ring

theorem markedDyadicPolynomial_sparse_energy (L R : ℕ) (H : ℝ)
    (a : ℕ → ℂ) (S : Finset ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hrow : ∀ t ∈ S, ∑ u ∈ S, ‖markedLogKernel L R (t-u)‖ ≤ B) :
    (∑ t ∈ S, ‖markedDyadicPolynomial L R H a t‖^2) ≤
      B * ∑ n ∈ Finset.Icc L R, ‖a n / H‖^2 := by
  simp_rw [markedDyadicPolynomial_eq_mrt]
  apply mrt_sparse_polynomial_energy _ _ _ _ hB
  simpa only [← markedLogKernel_eq_mrt] using hrow

/-- Transfer a pointwise reciprocal-plus-remainder kernel estimate to an
actual row sum. This finite algebraic lemma isolates no analytic assumption
in the eventual specialized kernel theorem. -/
theorem markedLogKernel_row_of_pointwise (L R : ℕ) (U A E T : ℝ)
    (hU : 0 ≤ U) (hA : 0 ≤ A) (hT : 0 ≤ T) (S : Finset ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|)
    (hbound : ∀ t : ℝ, |t| ≤ T →
      ‖markedLogKernel L R t‖ ≤ A*(U/(1+|t|)+E))
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, |x-y| ≤ T) (t : ℝ) (ht : t ∈ S) :
    (∑ u ∈ S, ‖markedLogKernel L R (t-u)‖) ≤
      A*(2*U*(1+Real.log (T+1))+(S.card:ℝ)*E) := by
  calc
    _ ≤ ∑ u ∈ S, A*(U/(1+|t-u|)+E) :=
      Finset.sum_le_sum fun u hu => hbound (t-u) (hdiam t ht u hu)
    _ = A*(U*(∑ u ∈ S, 1/(1+|t-u|))+(S.card:ℝ)*E) := by
      simp only [div_eq_mul_inv, mul_add, Finset.mul_sum, Finset.sum_add_distrib,
        Finset.sum_const, nsmul_eq_mul]
      ring_nf
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hA
      have hh := SparsePhase.separated_harmonic_kernel_sum S hsep t T hT
        (hdiam t ht)
      nlinarith [mul_le_mul_of_nonneg_left hh hU]

theorem marked_nat_int_interval_sum (f : ℤ → ℂ) (L R : ℕ) :
    (∑ n ∈ Finset.Icc L R, f n) = ∑ n ∈ Finset.Icc (L:ℤ) R, f n := by
  apply Finset.sum_bij (fun (n : ℕ) (_ : n ∈ Finset.Icc L R) => (n:ℤ))
  · intro n hn
    obtain ⟨hnL,hnR⟩ := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hnL,by exact_mod_cast hnR⟩
  · intro n hn m hm hnm
    exact_mod_cast hnm
  · intro n hn
    obtain ⟨hnL,hnR⟩ := Finset.mem_Icc.mp hn
    have hn0 : 0 ≤ n := le_trans (Int.natCast_nonneg _) hnL
    refine ⟨n.toNat,?_,Int.toNat_of_nonneg hn0⟩
    apply Finset.mem_Icc.mpr
    constructor <;> omega
  · intro n _
    rfl

end
end ArtinMatthews
