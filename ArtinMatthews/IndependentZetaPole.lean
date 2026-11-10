module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import OAI.NumberTheory.SiegelZeros.Differentials.ZetaLogDerivative


set_option backward.privateInPublic true
@[expose] public section

/-! The character-strip pole input follows from the existing OAI pole-removed
zeta bound on the entire compact real interval. -/

noncomputable section

namespace Erdos970

noncomputable def logDerivZeta (s : ℂ) : ℂ :=
  deriv riemannZeta s / riemannZeta s

theorem uniform_bound_Z0 :
    ∃ δ0 > (0 : ℝ), ∃ C0 ≥ (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < δ0 →
      (-(logDerivZeta ((1 : ℂ) + δ))).re ≤ 1 / δ + C0 := by
  obtain ⟨C, hC, hb⟩ := OAI.SiegelZeros.Awei.W53.zeta_logDerivative_re_upper
  refine ⟨1, zero_lt_one, C, hC, ?_⟩
  intro δ hδ hδ1
  have h := hb (1 + δ) (by linarith) (by linarith)
  simpa only [Complex.ofReal_add, Complex.ofReal_one, add_sub_cancel_left,
    logDerivZeta, neg_div, add_comm C] using h

end Erdos970
