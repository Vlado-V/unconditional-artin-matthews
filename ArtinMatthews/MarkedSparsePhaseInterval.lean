module

public import ArtinMatthews.MarkedSparsePhaseKernel
public import ArtinMatthews.MarkedSparseIntervalEnergy
public import ArtinMatthews.MarkedSparseIntervals
public import ArtinMatthews.MarkedSparsePhaseContinuity
public import ArtinMatthews.MarkedSparsePhaseFinal
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Literal unit-interval supremum energy on the exceptional frequency
set of the actual shifted prime polynomial. The source of sparsity and
the actual dyadic coefficient polynomial are both retained. -/

namespace ArtinMatthews

open Filter
open scoped Topology BigOperators

noncomputable section

theorem unitInterval_abs_bound_of_witness {z : ℤ} {T t w : ℝ}
    (ht : t ∈ Set.Icc (z:ℝ) ((z:ℝ)+1))
    (hw : w ∈ Set.Icc (z:ℝ) ((z:ℝ)+1)) (hwT : |w| ≤ T) :
    |t| ≤ T+1 := by
  have htw : |t-w| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1,hw.2],
    by linarith [ht.2,hw.1]⟩
  calc
    |t| = |w+(t-w)| := by congr 1; ring
    _ ≤ |w|+|t-w| := abs_add_le _ _
    _ ≤ T+1 := add_le_add hwT htw

/-- The second conclusion of the sparse-frequency lemma, for the actual
unit intervals that meet the exceptional set. Uniformity includes every
real shift, character, prime subset, and bounded coefficient vector. -/
theorem marked_sparse_frequency_unitInterval_energy
    (c C₁ C₂ A d : ℝ) (hc : 0 < c) (hC₁ : 0 < C₁)
    (hC₂ : 0 < C₂) (hA : 0 ≤ A) (hd : 0 < d) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (Y T U M : ℝ) (L R : ℕ) (a : ℕ → ℂ),
        1 < Y → c*X^(1/(10:ℝ)) ≤ Real.log Y →
        Real.log Y ≤ C₁*X^(1/(5:ℝ)) → 1 < T → Real.log T ≤ C₂*X →
        Real.exp (d*X) ≤ U → U ≤ (L:ℝ) → (R:ℝ) ≤ 2*U →
        (∀ n ∈ Finset.Icc L R, ‖a n‖ ≤ M) →
        ∀ (k : ℕ) (χ : DirichletCharacter ℂ k) (ξ : ℝ) (P : Finset ℕ),
          (∀ p ∈ P, p.Prime) → (∀ p ∈ P, (p:ℝ) ≤ 2*Y) →
          ∀ I : Finset ℤ,
            (∀ z ∈ I, ∃ t ∈ Set.Icc (z:ℝ) ((z:ℝ)+1),
              |t| ≤ T ∧ X^(-A) ≤ ‖markedPrimePolynomial P Y χ ξ t‖) →
            (∑ z ∈ I, sSup ((fun t => ‖markedDyadicPolynomial L R U a t‖^2) ''
              Set.Icc (z:ℝ) ((z:ℝ)+1))) ≤ K*X*M^2 := by
  obtain ⟨K₀,hK₀,henergy⟩ := markedDyadicPolynomial_sparse_energy_exp_range
    d (C₂+1) 1 3 hd (by linarith)
  refine ⟨3*K₀,by positivity,?_⟩
  filter_upwards [henergy,
    markedPrimePolynomial_sparse_unitIntervals c C₁ C₂ A hc hC₁ hC₂ hA,
    eventually_ge_atTop (Real.log 4)] with X henergy hcount hX
  intro Y T U M L R a hY hYlo hYhi hT hTlog hU hL hR ha
    k χ ξ P hP hPcap I hwitness
  have hcard : (I.card:ℝ) ≤ 3*Real.exp (X^(91/(100:ℝ))) :=
    hcount Y T hY hYlo hYhi hT hTlog k χ ξ P hP hPcap I hwitness
  have hTpos : 0 < T := by linarith
  have hheight : 2*(T+1) ≤ Real.exp ((C₂+1)*X) := by
    have hTe : T ≤ Real.exp (C₂*X) := by
      simpa only [Real.exp_log hTpos] using Real.exp_le_exp.mpr hTlog
    calc
      2*(T+1) ≤ 4*T := by linarith
      _ ≤ 4*Real.exp (C₂*X) := mul_le_mul_of_nonneg_left hTe (by norm_num)
      _ = Real.exp (Real.log 4+C₂*X) := by
        rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<4)]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have hclosure : ∀ z ∈ I, ∀ t ∈ Set.Icc (z:ℝ) ((z:ℝ)+1), |t| ≤ T+1 := by
    intro z hz t ht
    obtain ⟨w,hw,hwT,_⟩ := hwitness z hz
    exact unitInterval_abs_bound_of_witness ht hw hwT
  have hsamples : ∀ S : Finset ℝ, S.card ≤ I.card →
      (∀ t ∈ S, |t| ≤ T+1) →
      (∀ t ∈ S, ∀ u ∈ S, t ≠ u → 1 ≤ |t-u|) →
      (∑ t ∈ S, ‖markedDyadicPolynomial L R U a t‖^2) ≤ K₀*X*M^2 := by
    intro S hSI hS hsep
    have hcardS : (S.card:ℝ) ≤ 3*Real.exp (1*X^(91/(100:ℝ))) := by
      simpa only [one_mul] using
        (show (S.card:ℝ) ≤ I.card by exact_mod_cast hSI).trans hcard
    apply henergy U (2*(T+1)) M L R S a hU (by linarith) hheight hL hR ha hcardS hsep
    intro t ht u hu
    have htu : |t-u| ≤ |t|+|u| := abs_sub _ _
    linarith [hS t ht,hS u hu]
  calc
    _ ≤ 3*(K₀*X*M^2) := unitInterval_sum_sup_le I (fun t => |t| ≤ T+1)
      (fun t => ‖markedDyadicPolynomial L R U a t‖^2)
      (markedDyadicPolynomial_norm_sq_continuous L R U a) hclosure hsamples
    _ = _ := by ring

/- The two displayed conclusions are combined at the literal coefficient
scale `X^D`, retaining the closed-interval suprema. -/
theorem marked_sparse_frequency_unitIntervals
    (c C₁ C₂ A d D : ℝ) (hc : 0 < c) (hC₁ : 0 < C₁)
    (hC₂ : 0 < C₂) (hA : 0 ≤ A) (hd : 0 < d) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (Y T U : ℝ) (L R : ℕ) (a : ℕ → ℂ),
        1 < Y → c*X^(1/(10:ℝ)) ≤ Real.log Y →
        Real.log Y ≤ C₁*X^(1/(5:ℝ)) → 1 < T → Real.log T ≤ C₂*X →
        Real.exp (d*X) ≤ U → U ≤ (L:ℝ) → (R:ℝ) ≤ 2*U →
        (∀ n ∈ Finset.Icc L R, ‖a n‖ ≤ X^D) →
        ∀ (k : ℕ) (χ : DirichletCharacter ℂ k) (ξ : ℝ) (P : Finset ℕ),
          (∀ p ∈ P, p.Prime) → (∀ p ∈ P, (p:ℝ) ≤ 2*Y) →
          ∀ I : Finset ℤ,
            (∀ z ∈ I, ∃ t ∈ Set.Icc (z:ℝ) ((z:ℝ)+1),
              |t| ≤ T ∧ X^(-A) ≤ ‖markedPrimePolynomial P Y χ ξ t‖) →
            (I.card:ℝ) ≤ 3*Real.exp (X^(91/(100:ℝ))) ∧
            (∑ z ∈ I, sSup ((fun t => ‖markedDyadicPolynomial L R U a t‖^2) ''
              Set.Icc (z:ℝ) ((z:ℝ)+1))) ≤ K*X^(2*D+1) := by
  obtain ⟨K,hK,henergy⟩ := marked_sparse_frequency_unitInterval_energy
    c C₁ C₂ A d hc hC₁ hC₂ hA hd
  refine ⟨K,hK,?_⟩
  filter_upwards [henergy,
    markedPrimePolynomial_sparse_unitIntervals c C₁ C₂ A hc hC₁ hC₂ hA,
    eventually_gt_atTop (0:ℝ)] with X he hcX hX
  intro Y T U L R a hY hYlo hYhi hT hTlog hU hL hR ha
    k χ ξ P hP hPcap I hwitness
  refine ⟨hcX Y T hY hYlo hYhi hT hTlog k χ ξ P hP hPcap I hwitness,?_⟩
  have hpower : X*(X^D)^2 = X^(2*D+1) := by
    rw [← Real.rpow_mul_natCast hX.le]
    conv_lhs => lhs; rw [← Real.rpow_one X]
    rw [← Real.rpow_add hX]
    congr 1
    push_cast
    ring
  calc
    _ ≤ K*X*(X^D)^2 := he Y T U (X^D) L R a hY hYlo hYhi hT hTlog
      hU hL hR ha k χ ξ P hP hPcap I hwitness
    _ = _ := by rw [mul_assoc,hpower]

end
end ArtinMatthews
