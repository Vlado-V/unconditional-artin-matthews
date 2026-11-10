module

public import ArtinMatthews.MarkedMomentAmplification
public import ArtinMatthews.MarkedSparsePrimeMoments
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
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


set_option backward.privateInPublic true
@[expose] public section

/-! The literal shifted prime polynomial satisfies the optimized OAI sample
cost. No bound for a different coefficient vector is substituted. -/

namespace ArtinMatthews

open scoped BigOperators
open ReusedMoments

noncomputable section

theorem primeFinset_card_le_twice_scale (P : Finset ℕ) {H : ℝ}
    (hH : 0 < H) (hP : ∀ p ∈ P, p.Prime)
    (hcap : ∀ p ∈ P, (p : ℝ) ≤ 2*H) : (P.card : ℝ) ≤ 2*H := by
  have hsub : P ⊆ Finset.Ioc 0 ⌊2*H⌋₊ := by
    intro p hp
    apply Finset.mem_Ioc.mpr
    refine ⟨(hP p hp).pos, ?_⟩
    exact (Nat.le_floor_iff (by positivity)).mpr (hcap p hp)
  have hc := Finset.card_le_card hsub
  have hc' : (P.card : ℝ) ≤ (⌊2*H⌋₊ : ℝ) := by
    exact_mod_cast (by simpa using hc : P.card ≤ ⌊2*H⌋₊)
  exact hc'.trans (Nat.floor_le (by positivity))

theorem markedPrimePolynomial_sample_cost {k : ℕ}
    (P : Finset ℕ) (H : ℝ) (hH : 0 < H) (χ : DirichletCharacter ℂ k) (ξ : ℝ)
    (r : ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hcap : ∀ p ∈ P, (p : ℝ) ≤ 2*H)
    (S : Finset ℝ) {T V : ℝ} (hT : 0 ≤ T) (hV : 0 < V)
    (hS : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|)
    (hlarge : ∀ t ∈ S, V ≤ ‖markedPrimePolynomial P H χ ξ t‖) :
    (S.card : ℝ) ≤ mrtShortPrimeSampleCost H V T r := by
  have hn : ∀ p ∈ P, p ≤ 2*⌈H⌉₊ := by
    intro p hp
    have hh := (hcap p hp).trans
      (mul_le_mul_of_nonneg_left (Nat.le_ceil H) (by norm_num : (0:ℝ) ≤ 2))
    exact_mod_cast hh
  have hc := primeFinset_card_le_twice_scale P hH hP hcap
  have hm : (P.card : ℝ) / H^2 ≤ 2/H := by
    apply (div_le_iff₀ (sq_pos_of_pos hH)).mpr
    calc
      _ ≤ 2*H := hc
      _ = 2/H * H^2 := by field_simp
  apply (markedPrimePolynomial_large_values P H hH χ ξ (2*⌈H⌉₊) r
    hP hn S hT hV hS hsep hlarge).trans
  unfold mrtShortPrimeSampleCost
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hm r) (by positivity)

/-- The optimized cost is uniform in the real shift and character. -/
theorem markedPrimePolynomial_optimized_count {k : ℕ}
    (P : Finset ℕ) (H : ℝ) (hH : 1 < H) (χ : DirichletCharacter ℂ k) (ξ : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hcap : ∀ p ∈ P, (p : ℝ) ≤ 2*H)
    (S : Finset ℝ) {T V : ℝ} (hT : 1 < T) (hV : 0 < V)
    (hS : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|)
    (hlarge : ∀ t ∈ S, V ≤ ‖markedPrimePolynomial P H χ ξ t‖) :
    (S.card : ℝ) ≤
      24*Real.exp 1*(2+((mrtAmplificationOrder H T : ℝ)*Real.log (4*H))^2)*
        Real.exp ((mrtAmplificationOrder H T : ℝ)*
          (Real.log (8*(mrtAmplificationOrder H T : ℝ))-2*Real.log V)) := by
  exact (markedPrimePolynomial_sample_cost P H (by linarith) χ ξ
    (mrtAmplificationOrder H T) hP hcap S (by linarith) hV hS hsep hlarge).trans
      (mrt_short_prime_sample_cost_exp hH hV hT)

end
end ArtinMatthews
