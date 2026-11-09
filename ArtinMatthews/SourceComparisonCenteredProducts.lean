module

public import ArtinMatthews.SourceComparisonProductEnergy
public import ArtinMatthews.SourceComparisonGiantCenter


set_option backward.privateInPublic true
@[expose] public section

/-! The centered high-frequency polynomial splits into the two original
product sums and the literal error from removing the small mark. -/

namespace ArtinMatthews

open Finset MeasureTheory
open scoped BigOperators

noncomputable section

def sourceComparisonHighMellin {q : ℕ} [NeZero q] (h : ZMod q)
    (W : ℕ → ℂ) (ψ : ℝ → ℂ) (Y b t : ℝ) : ℂ :=
  (∑ n ∈ Ioc 0 ⌊b*Y⌋₊, W n*ψ ((n:ℝ)/Y)*ZMod.stdAddChar (h*(n:ZMod q))*
    markedPrimePhase n t)/Y

theorem sourceComparisonHighMellin_eq_polynomial {q : ℕ} [NeZero q] (h : ZMod q)
    (W : ℕ → ℂ) (ψ : ℝ → ℂ) (Y b t : ℝ) :
    sourceComparisonHighMellin h W ψ Y b t =
      markedNaturalPolynomial (Ioc 0 ⌊b*Y⌋₊)
        (fun n => W n*ψ ((n:ℝ)/Y)*ZMod.stdAddChar (h*(n:ZMod q))/Y) t := by
  unfold sourceComparisonHighMellin markedNaturalPolynomial
  rw [sum_div]
  apply sum_congr rfl
  intro n _
  ring

theorem sourceComparisonHighMellin_continuous {q : ℕ} [NeZero q] (h : ZMod q)
    (W : ℕ → ℂ) (ψ : ℝ → ℂ) (Y b : ℝ) : Continuous (sourceComparisonHighMellin h W ψ Y b) := by
  unfold sourceComparisonHighMellin markedPrimePhase
  fun_prop

theorem sourceComparisonHighMellin_add {q : ℕ} [NeZero q] (h : ZMod q)
    (W W' : ℕ → ℂ) (ψ : ℝ → ℂ) (Y b t : ℝ) :
    sourceComparisonHighMellin h (fun n => W n+W' n) ψ Y b t =
      sourceComparisonHighMellin h W ψ Y b t+sourceComparisonHighMellin h W' ψ Y b t := by
  simp only [sourceComparisonHighMellin, add_mul, sum_add_distrib, add_div]

def sourceComparisonRemovedWeight (S : Finset ℕ) (β : ℕ → ℂ) (n : ℕ) : ℂ :=
  (bandReciprocalMass S:ℂ)⁻¹ * ∑ p ∈ activeDivisors S n, β (n/p)

theorem sourceComparisonHighMellin_centered_eq {q : ℕ} [NeZero q] (h : ZMod q)
    (W β : ℕ → ℂ) (S : Finset ℕ) (ψ : ℝ → ℂ) (a b Y x ε t : ℝ)
    (hx : 0 ≤ x) (hY : 0 < Y) (hsupp : Function.support ψ ⊆ Set.Icc a b)
    (hS : ∀ p ∈ S, p.Prime) (hdis : Disjoint S (giantPrimeWindow x ε))
    (hinv : ∀ m ∈ giantPrimeWindow x ε, ∀ n, β (m*n) = β n)
    (hcap : ∀ n ∈ Ioc 0 ⌊b*Y⌋₊, (n:ℝ) ≤ (x^(1-ε))^2) :
    sourceComparisonHighMellin h (fun n => W n*(giantMarkedCenteredCore ε x n:ℂ)) ψ Y b t =
      sourceComparisonHighMellin h (fun n =>
        (W n-sourceComparisonRemovedWeight S β n)*(giantMarkedCenteredCore ε x n:ℂ)) ψ Y b t +
      (bandReciprocalMass S:ℂ)⁻¹ *
        (sourceComparisonProductMellin h S (giantPrimeWindow x ε) (Ioc 0 ⌊b*Y⌋₊) β ψ Y t -
          (giantPrimeReciprocalSum x ε:ℂ) *
            sourceComparisonProductMellin h S {1} (Ioc 0 ⌊b*Y⌋₊) β ψ Y t) := by
  let G := giantPrimeWindow x ε
  let N := ⌊b*Y⌋₊
  let F (n : ℕ) := ψ ((n:ℝ)/Y)*ZMod.stdAddChar (h*(n:ZMod q))*markedPrimePhase n t
  let C (n : ℕ) := (giantMarkedCenteredCore ε x n:ℂ)
  let W₀ := sourceComparisonRemovedWeight S β
  have hF (n : ℕ) (hn : N < n) : F n = 0 := by
    have hz : ψ ((n:ℝ)/Y) = 0 := by
      by_contra hne
      have hn' : (n:ℝ) ≤ b*Y := (div_le_iff₀ hY).mp (hsupp hne).2
      have hbY : 0 ≤ b*Y := (Nat.cast_nonneg n).trans hn'
      exact (not_le_of_gt hn) ((Nat.le_floor_iff hbY).mpr hn')
    simp only [F, hz, zero_mul]
  have hC (n : ℕ) (hn : n ∈ Ioc 0 N) :
      C n = (giantWindowDivisorCount G n:ℂ)-(giantPrimeReciprocalSum x ε:ℂ) := by
    dsimp only [C]
    rw [sourceComparisonGiantCenter_eq_window (mem_Ioc.mp hn).1 hx (hcap n hn),
      Complex.ofReal_sub]
    rfl
  have hW (n : ℕ) : W n*C n = (W n-W₀ n)*C n+W₀ n*C n := by ring
  change sourceComparisonHighMellin h (fun n => W n*C n) ψ Y b t = _
  simp_rw [hW]
  rw [sourceComparisonHighMellin_add]
  apply congrArg (sourceComparisonHighMellin h (fun n => (W n-W₀ n)*C n) ψ Y b t + ·)
  have hlhs :
      sourceComparisonHighMellin h (fun n => W₀ n*C n) ψ Y b t =
        (∑ n ∈ Ioc 0 N, (bandReciprocalMass S:ℂ)⁻¹*(∑ p ∈ activeDivisors S n, β (n/p))*
          ((giantWindowDivisorCount G n:ℂ)-(giantPrimeReciprocalSum x ε:ℂ))*F n)/Y := by
    unfold sourceComparisonHighMellin
    congr 1
    apply sum_congr rfl
    intro n hn
    dsimp only
    rw [hC n hn]
    dsimp [W₀, sourceComparisonRemovedWeight, F]
    ring
  rw [hlhs, sourceComparison_removed_centered_eq S G N Y (giantPrimeReciprocalSum x ε) β F hS
    (fun p hp => ((mem_giantPrimeWindow hx).mp hp).1) hdis hinv hF]
  simp only [sourceComparisonProductMellin, sourceComparisonCutTriple, sourceComparisonProductCoefficient,
    sourceComparisonTriplePosition, sum_product, sum_singleton, mul_one]
  have hp (p m n : ℕ) :
      β n*ZMod.stdAddChar (h*((p*m*n:ℕ):ZMod q))*ψ (((p*m*n:ℕ):ℝ)/Y)*
        markedPrimePhase (p*m*n) t = β n*F (p*m*n) := by dsimp [F]; ring
  have hc (p n : ℕ) :
      β n*ZMod.stdAddChar (h*((p*n:ℕ):ZMod q))*ψ (((p*n:ℕ):ℝ)/Y)*
        markedPrimePhase (p*n) t = β n*F (p*n) := by dsimp [F]; ring
  simp_rw [hp, hc]
  ring

end
end ArtinMatthews
