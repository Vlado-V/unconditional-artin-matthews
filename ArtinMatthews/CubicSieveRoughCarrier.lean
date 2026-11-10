module

public import ArtinMatthews.PrimeExtractionPrimeRoughIdentity
public import ArtinMatthews.GiantMarkedCharacterCriterion
public import ArtinMatthews.GiantSamplingCofactors
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The rough cutoff from the top-down sieve uses the same actual shifted
coefficient and cutoff as the checked cubic prime-extraction reduction. -/

noncomputable section
namespace ArtinMatthews

open OAI OAI.SevenEighths
open scoped BigOperators Classical

def cubicSieveRoughThetaSum (η : HeckeFamily.Character) {M : ℕ}
    (χ : DirichletCharacter ℂ M) (H : ℕ → ℂ) (Φ : ℝ → ℝ) (ε γ x : ℝ) : ℂ :=
  ∑ u ∈ Finset.Icc 1 ⌊2 * x⌋₊, H u * giantMarkedCenteredCore ε x u *
    giantCubicSamplingKernel η χ Φ x 1 u *
      ((if MarkedRoughAbove (x ^ γ) (u + 1) then (1 : ℝ) else 0) : ℂ)

theorem cubicSieve_roughTheta_eq_actual {J : Type*} [Fintype J] (e : J → ℝ)
    (η : HeckeFamily.Character) {M : ℕ} (χ : DirichletCharacter ℂ M)
    (Φ : ℝ → ℝ) (hs : Function.support Φ ⊆ Set.Ioo 1 2)
    (ε γ : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    cubicSieveRoughThetaSum η χ (fun u => (literalMarkedArrayWeight e x u : ℂ)) Φ ε γ x =
      markedActualRoughThetaSum e η χ (giantMarkedCenteredCore ε) Φ 3 γ x := by
  let N := ⌊2 * x⌋₊
  let V := Finset.Icc 2 (N + 1)
  let U := Finset.Ioc 0 ⌊3 * x⌋₊
  let F (n : ℕ) : ℂ := if MarkedRoughAbove (x ^ γ) n then
    markedExtractionWeight e (giantMarkedCenteredCore ε) Φ x n * (idealThetaCoeff η n * χ n)
    else 0
  have hcap : N + 1 ≤ ⌊3 * x⌋₊ := Nat.le_floor (by
    push_cast
    linarith [Nat.floor_le (show 0 ≤ 2 * x by positivity)])
  have hsub : V ⊆ U := by
    intro n hn
    obtain ⟨h₁, h₂⟩ := Finset.mem_Icc.mp hn
    exact Finset.mem_Ioc.mpr ⟨by omega, h₂.trans hcap⟩
  have hsupport (n : ℕ) (hn : Φ (((n - 1 : ℕ) : ℝ) / x) ≠ 0) : n ∈ V := by
    have hx₀ := zero_lt_one.trans_le hx
    obtain ⟨h₁, h₂⟩ := hs hn
    have hlow := (lt_div_iff₀ hx₀).mp h₁
    have hhigh := (div_lt_iff₀ hx₀).mp h₂
    have hp : 0 < n - 1 := Nat.cast_pos.mp (lt_trans hx₀ (by simpa only [one_mul] using hlow))
    have ht : n - 1 ≤ N := Nat.le_floor hhigh.le
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  unfold cubicSieveRoughThetaSum markedActualRoughThetaSum roughPositiveUpTo
  rw [Finset.sum_filter]
  change (∑ u ∈ Finset.Icc 1 N, _) = ∑ n ∈ U, F n
  calc
    _ = ∑ n ∈ V, F n := by
      apply Finset.sum_bij (fun u _ => u + 1)
      · intro u hu
        obtain ⟨h₁, h₂⟩ := Finset.mem_Icc.mp hu
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · intro u _hu v _hv h
        omega
      · intro n hn
        obtain ⟨h₁, h₂⟩ := Finset.mem_Icc.mp hn
        exact ⟨n - 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro u _hu
        dsimp only [F, markedExtractionWeight]
        rw [Nat.add_sub_cancel]
        by_cases hr : MarkedRoughAbove (x ^ γ) (u + 1)
        · simp only [ite_eq_left hr, Complex.ofReal_one, mul_one, giantCubicSamplingKernel,
            one_dvd, ite_true]
          push_cast
          ring
        · simp only [ite_eq_right hr, mul_zero]
    _ = _ := by
      apply Finset.sum_subset hsub
      intro n _hn hnV
      have hz : Φ (((n - 1 : ℕ) : ℝ) / x) = 0 :=
        not_not.mp (fun h => hnV (hsupport n h))
      simp [F, markedExtractionWeight, hz]

end ArtinMatthews
