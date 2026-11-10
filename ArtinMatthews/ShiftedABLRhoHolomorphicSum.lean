module

public import ArtinMatthews.ShiftedABLRhoCommonTest
public import ArtinMatthews.SpectralJHolomorphicCoefficient
public import ArtinMatthews.ShiftedABLRhoCommonTransforms
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual common rho test has an absolutely summable holomorphic
weight sequence, uniformly in its oscillatory parameter. -/
namespace ArtinMatthews
noncomputable section

private theorem even_exp_sum_le (a : ℝ) (ha : 0 ≤ a) :
    Summable (fun j : ℕ => a^(2*j)/((2*j).factorial : ℝ)) ∧
      (∑' j : ℕ, a^(2*j)/((2*j).factorial : ℝ)) ≤ Real.exp a := by
  let g (n : ℕ) := a^n/(n.factorial : ℝ)
  have h : HasSum g (Real.exp a) := by
    simpa only [g,← Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp a
  have he : Function.Injective (fun j : ℕ => 2*j) := by
    intro i j hij
    dsimp only at hij
    omega
  have hs : Summable (fun j : ℕ => g (2*j)) := h.summable.comp_injective he
  have hle : (∑' j : ℕ, g (2*j)) ≤ ∑' n : ℕ, g n :=
    hs.tsum_le_tsum_of_inj (fun j : ℕ => 2*j) he
      (fun n _ => by dsimp only [g]; positivity) (fun _ => le_rfl) h.summable
  exact ⟨hs,hle.trans_eq h.tsum_eq⟩

theorem shiftedABLRhoCommonTest_holomorphic_sum_bound (Rmax : ℝ) (hRmax : 0 ≤ Rmax) :
    ∃ C : ℝ, 0 < C ∧ ∀ a u : ℝ, 0 < a → a ≤ Rmax →
      Summable (fun j : ℕ => ‖spectralJHolomorphicCoefficient (shiftedABLRhoCommonTest a u) (2*j+2)‖) ∧
      (∑' j : ℕ, ‖spectralJHolomorphicCoefficient (shiftedABLRhoCommonTest a u) (2*j+2)‖) ≤
        C*a*Real.exp a := by
  obtain ⟨C,hC,hcoeff⟩ := shiftedABLRhoCommonTest_holomorphic_factorial Rmax hRmax
  refine ⟨C,hC,?_⟩
  intro a u ha haR
  let e (j : ℕ) := a^(2*j)/((2*j).factorial : ℝ)
  obtain ⟨he,hes⟩ := even_exp_sum_le a ha.le
  have hdom (j : ℕ) : ‖spectralJHolomorphicCoefficient (shiftedABLRhoCommonTest a u) (2*j+2)‖ ≤
      (C*a)*e j := by
    have h := hcoeff a u ha haR (2*j+2) (by omega)
    rw [show 2*j+2-1=2*j+1 by omega, show 2*j+2-2=2*j by omega,pow_succ] at h
    exact h.trans_eq (by dsimp only [e]; ring)
  have hm : Summable (fun j : ℕ => (C*a)*e j) := he.mul_left _
  have hs := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hdom hm
  refine ⟨hs,?_⟩
  calc
    _ ≤ ∑' j : ℕ, (C*a)*e j := hs.tsum_le_tsum hdom hm
    _ = (C*a)*(∑' j : ℕ, e j) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left hes (mul_nonneg hC.le ha.le)

end
end ArtinMatthews
