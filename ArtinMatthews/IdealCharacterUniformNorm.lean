module

public import ArtinMatthews.IdealCharacterUniformInput
public import ArtinMatthews.IdealCharacterCellApply
public import ArtinMatthews.IdealCharacterReproductionActual
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The norm bound is uniform over finite slot carriers, including
families whose number of groups varies with the source parameter. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable
universe u

theorem idealCharacterCellApply_of_primeInput {I : Type*} [Fintype I] [DecidableEq I]
    {L c d v₀ ε ξ : ℝ} {Q : ℕ} (hinput : IdealPrimeCharacterInput L c d v₀ Q ε)
    (hε : 0 ≤ ε) (hξ : 0 < ξ) (hbudget : (Q : ℝ)^2*ε ≤ ξ)
    (P : I → Finset ℕ) (hP : ∀ i p, p ∈ P i → p.Prime)
    (hV : ∀ i, 0 < bandReciprocalMass (P i))
    (hlarge : ∀ i p, p ∈ P i → Q < p) (i : I)
    (hinterval : IdealPrimeInterval (P i))
    (hbounds : ∀ p ∈ P i, Real.exp (L^c) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (L^d))
    (hVlo : v₀ ≤ bandReciprocalMass (P i)) (h : ℝ) (hh : 0 < h)
    (f : IdealSelectedLabels P → ℂ) :
    idealFrameEnergy (idealSelectedMass P) (idealCharacterCellApply P Q h ξ f) ≤
      4*idealFrameEnergy (idealSelectedMass P) f := by
  apply idealCharacterCellApply_energy_le P hV Q h hξ (by norm_num)
  intro j hj g
  have hm : 0 < idealLogCellMass P h j := hξ.trans_le hj
  have hcf := idealConditionalCharacterFrame_energy_le P hV Q h j hP hlarge hε hm
    (fun χ ψ hne => idealCharacterCellGram_of_primeInput hinput P hP hV i hinterval hbounds hVlo h hh j χ ψ hne) g
  have hr : (Q : ℝ)^2*(ε/idealLogCellMass P h j) ≤ 1 := by
    rw [← mul_div_assoc]
    exact (div_le_one₀ hm).mpr (hbudget.trans hj)
  have hp : 0 ≤ (Q : ℝ)^2*(ε/idealLogCellMass P h j) := by positivity
  have hs : (1+(Q : ℝ)^2*(ε/idealLogCellMass P h j))^2 ≤ 4 := by nlinarith
  exact hcf.trans (mul_le_mul_of_nonneg_right hs
    (idealFrameEnergy_nonneg _ (idealCellConditionalMass_nonneg P hV h j) g))

theorem idealCharacterCellApply_uniform (a c d X v₀ : ℝ)
    (ha : 0 ≤ a) (hc : 0 < c) (hd : 0 ≤ d) (hX : 0 ≤ X) (hv₀ : 0 < v₀) :
    ∀ᶠ L : ℝ in atTop, ∀ (I : Type u) [Fintype I] [DecidableEq I],
      ∀ (Q : ℕ), (Q : ℝ) ≤ L^a →
      ∀ (P : I → Finset ℕ), (∀ i p, p ∈ P i → p.Prime) →
      (∀ i, 0 < bandReciprocalMass (P i)) →
      (∀ i p, p ∈ P i → Real.exp (L^c) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (L^d)) →
      ∀ i : I, IdealPrimeInterval (P i) → v₀ ≤ bandReciprocalMass (P i) →
      ∀ h : ℝ, 0 < h → ∀ f : IdealSelectedLabels P → ℂ,
        idealFrameEnergy (idealSelectedMass P) (idealCharacterCellApply P Q h (L^(-X)) f) ≤
          4*idealFrameEnergy (idealSelectedMass P) f := by
  filter_upwards [idealPrimeCharacterInput_eventually a c d (2*a+X) v₀ ha hc hd (by positivity) hv₀,
    idealSource_prime_gt_conductor a c hc, eventually_gt_atTop (0 : ℝ)] with L hinput hsize hL
  intro I _ _ Q hQ P hP hV hbounds i hinterval hVlo h hh f
  have hbudget : (Q : ℝ)^2*L^(-(2*a+X)) ≤ L^(-X) := by
    have hQ2 : (Q : ℝ)^2 ≤ L^(2*a) := by
      calc
        _ ≤ (L^a)^2 := pow_le_pow_left₀ (Nat.cast_nonneg Q) hQ 2
        _ = _ := by rw [← Real.rpow_two, ← Real.rpow_mul hL.le]; congr 1; ring
    calc
      _ ≤ L^(2*a)*L^(-(2*a+X)) := mul_le_mul_of_nonneg_right hQ2 (Real.rpow_nonneg hL.le _)
      _ = _ := by rw [← Real.rpow_add hL]; congr 1; ring
  exact idealCharacterCellApply_of_primeInput (hinput Q hQ) (Real.rpow_nonneg hL.le _)
    (Real.rpow_pos_of_pos hL _) hbudget P hP hV
    (fun k p hp => hsize Q p hQ (hbounds k p hp).1) i hinterval (hbounds i) hVlo h hh f

end
end ArtinMatthews
