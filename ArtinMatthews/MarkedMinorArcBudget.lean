module

public import ArtinMatthews.MarkedMinorArcDeterminant
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual determinant Gram budget has the clean minor-arc decay after
the source lattice-box bounds. Constants are independent of the box origins,
coefficients and rational numerator. -/
namespace ArtinMatthews

/-- Normalize the proved Gram budget by the determinant scale `Y`, retaining
only the actual rational denominator window and lattice side bounds. -/
theorem marked_minor_gram_budget_normalized {M N q : ℕ} {Y Q C : ℝ}
    (hN : 1 ≤ N) (hC : 1 ≤ C) (hY : 1 ≤ Y) (hQ : 1 ≤ Q)
    (hq : Q ≤ (q : ℝ)) (hqY : (q : ℝ) ≤ Y/Q)
    (hMN : (M : ℝ)*(N : ℝ) ≤ C*Y)
    (hM : (M : ℝ) ≤ C*Y^(9/10 : ℝ)) (hNs : (N : ℝ) ≤ C*Y^(9/10 : ℝ)) :
    markedMinorGramBudget M N q / Y ≤
      (12*C+4)*(1+Real.log (2*Y))/Q +
        26*C*Y^(-1/10 : ℝ)*(1+Real.log (2*Y)) := by
  have hYp : 0 < Y := by linarith
  have hQp : 0 < Q := by linarith
  have hCp : 0 < C := by linarith
  have hqp : (0 : ℝ) < q := hQp.trans_le hq
  have hqY' : (q : ℝ) ≤ Y := hqY.trans (div_le_self hYp.le hQ)
  let H := 1+Real.log (2*Y)
  have hH : 1 ≤ H := by
    have hh := Real.log_nonneg (show 1 ≤ 2*Y by linarith)
    dsimp [H]
    linarith
  have hlog : 1+Real.log (2*(q : ℝ)) ≤ H := by
    apply add_le_add_right
    exact Real.log_le_log (by positivity) (by linarith)
  have hH0 : 0 ≤ H := by linarith
  have hHq0 : 0 ≤ 1+Real.log (2*(q : ℝ)) := by
    have hh := Real.log_nonneg (show 1 ≤ 2*(q : ℝ) by linarith)
    linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hfirst : 2*((2*N+1 : ℕ) : ℝ)/(q : ℝ)+1 ≤ 6*(N : ℝ)/(q : ℝ)+1 := by
    push_cast
    apply add_le_add_left
    exact div_le_div_of_nonneg_right (by linarith) hqp.le
  have hterm1 : 12*((M : ℝ)*(N : ℝ))/(q : ℝ) ≤ 12*(C*Y)/Q := by
    have hh := (div_le_div_of_nonneg_right hMN hqp.le).trans
      (div_le_div_of_nonneg_left (show 0 ≤ C*Y by positivity) hQp hq)
    calc
      _ = 12*(((M : ℝ)*(N : ℝ))/(q : ℝ)) := by ring
      _ ≤ 12*((C*Y)/Q) := mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = _ := by ring
  have hMmul : C*Y^(9/10 : ℝ) ≤ C*Y^(9/10 : ℝ)*H := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hH
      (show 0 ≤ C*Y^(9/10 : ℝ) by positivity)
  have hterm2 : 2*(M : ℝ) ≤ 2*(C*Y^(9/10 : ℝ)*H) :=
    mul_le_mul_of_nonneg_left (hM.trans hMmul) (by norm_num)
  have hterm3 : 24*(N : ℝ)*H ≤ 24*(C*Y^(9/10 : ℝ))*H :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNs (by norm_num)) hH0
  have hterm4 : 4*(q : ℝ)*H ≤ 4*(Y/Q)*H :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqY (by norm_num)) hH0
  have hb : markedMinorGramBudget M N q ≤
      12*C*Y/Q + 26*C*Y^(9/10 : ℝ)*H + 4*(Y/Q)*H := by
    calc
      _ ≤ (6*(N : ℝ)/(q : ℝ)+1)*(2*(M : ℝ)+4*(q : ℝ)*H) := by
        unfold markedMinorGramBudget
        gcongr
      _ = 12*((M : ℝ)*(N : ℝ))/(q : ℝ)+2*(M : ℝ)+24*(N : ℝ)*H+4*(q : ℝ)*H := by
        field_simp
        ring
      _ ≤ 12*(C*Y)/Q + 2*(C*Y^(9/10 : ℝ)*H) +
          24*(C*Y^(9/10 : ℝ))*H + 4*(Y/Q)*H :=
        add_le_add (add_le_add (add_le_add hterm1 hterm2) hterm3) hterm4
      _ = _ := by ring
  have hb' : markedMinorGramBudget M N q ≤
      (12*C*Y/Q)*H + 26*C*Y^(9/10 : ℝ)*H + 4*(Y/Q)*H := by
    refine hb.trans ?_
    have hh : 12*C*Y/Q ≤ (12*C*Y/Q)*H := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hH
        (show 0 ≤ 12*C*Y/Q by positivity)
    exact add_le_add (add_le_add hh le_rfl) le_rfl
  apply (div_le_iff₀ hYp).mpr
  refine hb'.trans_eq ?_
  rw [show (9/10 : ℝ) = 1+(-1/10) by ring,Real.rpow_add hYp,Real.rpow_one]
  dsimp [H]
  ring


/-- The actual normalized determinant transform satisfies the clean L²
bound supplied by the source rational window and lattice-box inequalities. -/
theorem marked_minor_normalized_determinant_energy_le (L T : ℤ) (M N : ℕ)
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ-(a : ℝ)/q| ≤ 1/(q : ℝ)^2) {Y Q C : ℝ}
    (hMpos : 1 ≤ M) (hNpos : 1 ≤ N) (hC : 1 ≤ C) (hY : 1 ≤ Y) (hQ : 1 ≤ Q)
    (hQq : Q ≤ (q : ℝ)) (hqY : (q : ℝ) ≤ Y/Q)
    (hMN : (M : ℝ)*(N : ℝ) ≤ C*Y)
    (hM : (M : ℝ) ≤ C*Y^(9/10 : ℝ)) (hN : (N : ℝ) ≤ C*Y^(9/10 : ℝ))
    (c : ℤ × ℤ → ℂ) :
    (∑ h₁ ∈ Finset.Ico L (L+(M : ℤ)), ∑ h₂ ∈ Finset.Ico T (T+(N : ℤ)),
      ‖((Y : ℂ)⁻¹) * markedMinorDeterminantTransform L T M N θ c h₁ h₂‖^2) ≤
      ((12*C+4)*(1+Real.log (2*Y))/Q +
        26*C*Y^(-1/10 : ℝ)*(1+Real.log (2*Y)))^2 *
          (∑ l₁ ∈ Finset.Ico L (L+(M : ℤ)), ∑ l₂ ∈ Finset.Ico T (T+(N : ℤ)), ‖c (l₁,l₂)‖^2) := by
  have hYp : 0 < Y := by linarith
  let B := (12*C+4)*(1+Real.log (2*Y))/Q +
    26*C*Y^(-1/10 : ℝ)*(1+Real.log (2*Y))
  have hb₁ : markedMinorGramBudget M N q/Y ≤ B :=
    marked_minor_gram_budget_normalized hNpos hC hY hQ hQq hqY hMN hM hN
  have hb₂ : markedMinorGramBudget N M q/Y ≤ B :=
    marked_minor_gram_budget_normalized hMpos hC hY hQ hQq hqY
      (by simpa only [mul_comm] using hMN) hN hM
  have hg₁ := markedMinorGramBudget_nonneg M N q hq
  have hg₂ := markedMinorGramBudget_nonneg N M q hq
  have hB : 0 ≤ B := (div_nonneg hg₁ hYp.le).trans hb₁
  have hprod : (markedMinorGramBudget M N q/Y)*(markedMinorGramBudget N M q/Y) ≤ B^2 := by
    simpa only [pow_two] using mul_le_mul hb₁ hb₂ (div_nonneg hg₂ hYp.le) hB
  have hbase := marked_minor_determinant_energy_le L T M N θ a q hq hcop happrox c
  have hpt (h₁ h₂ : ℤ) :
      ‖((Y : ℂ)⁻¹) * markedMinorDeterminantTransform L T M N θ c h₁ h₂‖^2 =
      ‖markedMinorDeterminantTransform L T M N θ c h₁ h₂‖^2/Y^2 := by
    simp only [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hYp,mul_pow,inv_pow]
    ring
  simp_rw [hpt]
  calc
    _ ≤ (markedMinorGramBudget M N q * markedMinorGramBudget N M q *
        (∑ l₁ ∈ Finset.Ico L (L+(M : ℤ)), ∑ l₂ ∈ Finset.Ico T (T+(N : ℤ)), ‖c (l₁,l₂)‖^2))/Y^2 :=
      by simpa only [Finset.sum_div] using div_le_div_of_nonneg_right hbase (sq_nonneg Y)
    _ = ((markedMinorGramBudget M N q/Y)*(markedMinorGramBudget N M q/Y))*
        (∑ l₁ ∈ Finset.Ico L (L+(M : ℤ)), ∑ l₂ ∈ Finset.Ico T (T+(N : ℤ)), ‖c (l₁,l₂)‖^2) := by
      rw [pow_two]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hprod (by positivity)

end ArtinMatthews
