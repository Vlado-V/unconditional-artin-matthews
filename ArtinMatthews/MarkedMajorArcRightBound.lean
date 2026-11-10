module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.Chebyshev
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
public import OAI.NumberTheory.SiegelZeros.Differentials.ZetaLogDerivative


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform right-half-plane bounds for every Dirichlet character and every
height, derived from the actual absolutely convergent von Mangoldt series.
The source comparison and pole-removed zeta argument are recorded separately. -/
namespace ArtinMatthews

open ArithmeticFunction DirichletCharacter
open scoped LSeries.notation BigOperators ComplexOrder

theorem marked_major_logderiv_le_zeta {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    ‖deriv (LFunction χ) s / LFunction χ s‖ ≤
      (-deriv riemannZeta (s.re : ℂ) / riemannZeta (s.re : ℂ)).re := by
  have htw := LSeriesSummable_twist_vonMangoldt χ hs
  have hΛ := LSeriesSummable_vonMangoldt (show 1 < (s.re : ℂ).re from hs)
  calc
    ‖deriv (LFunction χ) s / LFunction χ s‖ = ‖LSeries (↗χ * ↗Λ) s‖ := by
      rw [LSeries_twist_vonMangoldt_eq χ hs,
        deriv_LFunction_eq_deriv_LSeries χ hs, LFunction_eq_LSeries χ hs]
      simp [neg_div]
    _ ≤ ∑' n, ‖LSeries.term (↗χ * ↗Λ) s n‖ := norm_tsum_le_tsum_norm htw.norm
    _ ≤ ∑' n, ‖LSeries.term ↗Λ (s.re : ℂ) n‖ := by
      apply htw.norm.tsum_le_tsum _ hΛ.norm
      intro n
      have hcoeff : ‖(↗χ * ↗Λ) n‖ ≤ ‖(↗Λ n : ℂ)‖ := by
        simpa using mul_le_of_le_one_left (norm_nonneg (vonMangoldt n : ℂ))
          (χ.norm_le_one (n : ZMod q))
      simpa only [LSeries.norm_term_eq, Complex.ofReal_re] using
        (LSeries.norm_term_le (f := ↗χ * ↗Λ) (g := ↗Λ) (n := n) s hcoeff)
    _ = (LSeries ↗Λ (s.re : ℂ)).re := by
      rw [LSeries, Complex.re_tsum hΛ]
      apply tsum_congr
      intro n
      have hn : 0 ≤ LSeries.term ↗Λ (s.re : ℂ) n :=
        LSeries.term_nonneg (by exact_mod_cast (vonMangoldt_nonneg (n := n))) s.re
      simpa using congrArg Complex.re (RCLike.norm_of_nonneg' hn)
    _ = (-deriv riemannZeta (s.re : ℂ) / riemannZeta (s.re : ℂ)).re :=
      congrArg Complex.re (LSeries_vonMangoldt_eq_deriv_riemannZeta_div (show 1 < (s.re : ℂ).re from hs))


/-- A uniform bound on the entire right vertical line, including its
unbounded tails. No high-height cancellation assumption is used. -/
theorem marked_major_logderiv_right_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q]
      (χ : DirichletCharacter ℂ q) (s : ℂ), 1 < s.re → s.re ≤ 2 →
      ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ C + 1/(s.re-1) := by
  obtain ⟨C,hC,hz⟩ := OAI.SiegelZeros.Awei.W53.zeta_logDerivative_re_upper
  exact ⟨C,hC,fun q _ χ s hs hs2 =>
    (marked_major_logderiv_le_zeta χ hs).trans (hz s.re hs hs2)⟩

end ArtinMatthews
