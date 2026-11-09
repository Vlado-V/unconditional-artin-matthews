module

public import ArtinMatthews.SpectralDyadicPartition
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.Real


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute-convergence-preserving decomposition into the two interlaced
smooth dyadic families. The original coefficient sum is unchanged. -/
namespace ArtinMatthews

open scoped BigOperators
noncomputable section

def spectralDyadicCoefficient (a : ℂ) (n m : ℕ) (d : ℕ × ℕ) : ℂ :=
  a * ((spectralDyadicBlock d.1 n * spectralDyadicBlock d.2 m : ℝ) : ℂ)

lemma hasSum_spectralDyadicPair (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    HasSum (fun d : ℕ × ℕ => spectralDyadicBlock d.1 n * spectralDyadicBlock d.2 m) 1 := by
  have Hn := hasSum_spectralDyadicBlock n hn
  have Hm := hasSum_spectralDyadicBlock m hm
  have Hp := summable_mul_of_summable_norm Hn.summable.norm Hm.summable.norm
  simpa only [mul_one] using Hn.mul Hm Hp

lemma hasSum_spectralDyadicCoefficient (a : ℂ) (n m : ℕ)
    (hn : 1 ≤ n) (hm : 1 ≤ m) : HasSum (spectralDyadicCoefficient a n m) a := by
  change HasSum (fun d : ℕ × ℕ => a * ((spectralDyadicBlock d.1 n * spectralDyadicBlock d.2 m : ℝ) : ℂ)) a
  have H := Complex.hasSum_ofReal.mpr (hasSum_spectralDyadicPair n m hn hm)
  simpa [spectralDyadicCoefficient] using H.mul_left a

lemma hasSum_norm_spectralDyadicCoefficient (a : ℂ) (n m : ℕ)
    (hn : 1 ≤ n) (hm : 1 ≤ m) :
    HasSum (fun d => ‖spectralDyadicCoefficient a n m d‖) ‖a‖ := by
  have he : (fun d => ‖spectralDyadicCoefficient a n m d‖) =
      (fun d : ℕ × ℕ => ‖a‖ * (spectralDyadicBlock d.1 n * spectralDyadicBlock d.2 m)) := by
    funext d
    rw [spectralDyadicCoefficient,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (spectralDyadicBlock_nonneg _ _) (spectralDyadicBlock_nonneg _ _))]
  rw [he]
  simpa only [mul_one] using (hasSum_spectralDyadicPair n m hn hm).mul_left ‖a‖

lemma hasSum_spectralDyadicCoefficient_of_nonzero (a : ℂ) (n m : ℕ)
    (hn : a ≠ 0 → 1 ≤ n) (hm : a ≠ 0 → 1 ≤ m) :
    HasSum (spectralDyadicCoefficient a n m) a := by
  by_cases ha : a = 0
  · subst a
    change HasSum (fun d : ℕ × ℕ => (0 : ℂ) * ((spectralDyadicBlock d.1 n * spectralDyadicBlock d.2 m : ℝ) : ℂ)) 0
    simp
  · exact hasSum_spectralDyadicCoefficient a n m (hn ha) (hm ha)

lemma hasSum_norm_spectralDyadicCoefficient_of_nonzero (a : ℂ) (n m : ℕ)
    (hn : a ≠ 0 → 1 ≤ n) (hm : a ≠ 0 → 1 ≤ m) :
    HasSum (fun d => ‖spectralDyadicCoefficient a n m d‖) ‖a‖ := by
  by_cases ha : a = 0
  · subst a
    simp [spectralDyadicCoefficient]
  · exact hasSum_norm_spectralDyadicCoefficient a n m (hn ha) (hm ha)

theorem spectralDyadic_expansion_summable {ι : Type*}
    (a : ι → ℂ) (n m : ι → ℕ) (ha : Summable a)
    (hn : ∀ p, a p ≠ 0 → 1 ≤ n p) (hm : ∀ p, a p ≠ 0 → 1 ≤ m p) :
    Summable (fun z : ι × (ℕ × ℕ) => spectralDyadicCoefficient (a z.1) (n z.1) (m z.1) z.2) := by
  have H (p : ι) := hasSum_norm_spectralDyadicCoefficient_of_nonzero
    (a p) (n p) (m p) (hn p) (hm p)
  apply Summable.of_norm
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).2
  refine ⟨fun p => (H p).summable,?_⟩
  convert ha.norm using 1
  funext p
  exact (H p).tsum_eq

theorem spectralDyadic_reassembly {ι : Type*}
    (a : ι → ℂ) (n m : ι → ℕ) (ha : Summable a)
    (hn : ∀ p, a p ≠ 0 → 1 ≤ n p) (hm : ∀ p, a p ≠ 0 → 1 ≤ m p) :
    (∑' p, a p) = ∑' d : ℕ × ℕ, ∑' p,
      spectralDyadicCoefficient (a p) (n p) (m p) d := by
  have H := spectralDyadic_expansion_summable a n m ha hn hm
  calc
    _ = ∑' p, ∑' d : ℕ × ℕ, spectralDyadicCoefficient (a p) (n p) (m p) d := by
      apply tsum_congr
      intro p
      exact (hasSum_spectralDyadicCoefficient_of_nonzero (a p) (n p) (m p) (hn p) (hm p)).tsum_eq.symm
    _ = _ := H.tsum_comm.symm

theorem spectralDyadic_norm_reassembly {ι : Type*}
    (a : ι → ℂ) (n m : ι → ℕ) (ha : Summable a)
    (hn : ∀ p, a p ≠ 0 → 1 ≤ n p) (hm : ∀ p, a p ≠ 0 → 1 ≤ m p) :
    (∑' z : ι × (ℕ × ℕ), ‖spectralDyadicCoefficient (a z.1) (n z.1) (m z.1) z.2‖) =
      ∑' p, ‖a p‖ := by
  have H := (spectralDyadic_expansion_summable a n m ha hn hm).norm
  rw [H.tsum_prod]
  apply tsum_congr
  intro p
  exact (hasSum_norm_spectralDyadicCoefficient_of_nonzero (a p) (n p) (m p) (hn p) (hm p)).tsum_eq

end
end ArtinMatthews
