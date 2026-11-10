module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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

/-! Uniform subpower bound for the finite Euler factor in Rankin's count.
Only finitely many small prime factors contribute to the constant. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Topology
noncomputable section

theorem shiftedSmooth_euler_subpower (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ d : ℕ, 0<d →
      (∏ p ∈ d.primeFactors, (1-(p : ℝ)^(-ε))⁻¹) ≤ C*(d : ℝ)^ε := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)^ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (2:ℝ)))
  let f : ℕ → ℝ := fun p => (1-(p : ℝ)^(-ε))⁻¹
  let P := (Finset.range N).filter Nat.Prime
  let C : ℝ := ∏ p ∈ P, f p
  have hf (p : ℕ) (hp : p.Prime) : 0<f p ∧ 1≤f p := by
    have hp0 : (0:ℝ)<p := by exact_mod_cast hp.pos
    have hpow : (p:ℝ)^(-ε)<1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
    have hden : 0<1-(p:ℝ)^(-ε) := sub_pos.mpr hpow
    refine ⟨inv_pos.mpr hden,?_⟩
    change 1 ≤ (1-(p:ℝ)^(-ε))⁻¹
    rw [← one_div]
    exact (one_le_div hden).mpr (by linarith [Real.rpow_pos_of_pos hp0 (-ε)])
  have hC : 0<C := Finset.prod_pos (fun p hp => (hf p (Finset.mem_filter.mp hp).2).1)
  refine ⟨C,hC,?_⟩
  intro d hd
  let E := d.primeFactors
  let S := E.filter (fun p => p<N)
  let T := E.filter (fun p => ¬p<N)
  have hprime {p : ℕ} (hp : p∈E) : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hS : S⊆P := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Finset.mem_filter.mp hp).2,
      hprime (Finset.mem_filter.mp hp).1⟩
  have hsmall : (∏ p∈S,f p) ≤ C := by
    apply Finset.prod_le_prod_of_subset_of_one_le₀ hS
    · intro p hp
      exact (hf p (hprime (Finset.mem_filter.mp hp).1)).1.le
    · intro p hp _
      exact (hf p (Finset.mem_filter.mp hp).2).2
  have hlarge : (∏ p∈T,f p) ≤ ∏ p∈T,(p:ℝ)^ε := by
    apply Finset.prod_le_prod₀
    · intro p hp
      exact (hf p (hprime (Finset.mem_filter.mp hp).1)).1.le
    · intro p hp
      have hpp := hprime (Finset.mem_filter.mp hp).1
      have hp0 : (0:ℝ)<p := by exact_mod_cast hpp.pos
      have hpow := hN p (Nat.le_of_not_gt (Finset.mem_filter.mp hp).2)
      have hden : 0<1-(p:ℝ)^(-ε) := sub_pos.mpr
        (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hpp.one_lt) (by linarith))
      change (1-(p:ℝ)^(-ε))⁻¹ ≤ (p:ℝ)^ε
      rw [← one_div, div_le_iff₀ hden, Real.rpow_neg hp0.le]
      nlinarith [mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hp0 ε))]
  have hprod : (∏ p∈T,(p:ℝ)^ε) ≤ (d:ℝ)^ε := by
    calc
      _ ≤ ∏ p∈E,(p:ℝ)^ε := by
        apply Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.filter_subset _ _)
        · intro p _; positivity
        · intro p hp _
          exact Real.one_le_rpow (by exact_mod_cast (hprime hp).one_lt.le) hε.le
      _ = (∏ p∈E,(p:ℝ))^ε := Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p) ε
      _ ≤ (d:ℝ)^ε := by
        apply Real.rpow_le_rpow (by positivity) _ hε.le
        dsimp only [E]
        rw [← Nat.cast_prod]
        exact_mod_cast Nat.le_of_dvd hd (Nat.prod_primeFactors_dvd d)
  have hsplit : (∏ p∈E,f p)=(∏ p∈S,f p)*(∏ p∈T,f p) :=
    (Finset.prod_filter_mul_prod_filter_not E (fun p => p<N) f).symm
  change (∏ p∈E,f p) ≤ C*(d:ℝ)^ε
  rw [hsplit]
  exact (mul_le_mul hsmall hlarge (Finset.prod_nonneg (fun p hp =>
    (hf p (hprime (Finset.mem_filter.mp hp).1)).1.le)) hC.le).trans
      (mul_le_mul_of_nonneg_left hprod hC.le)

end
end ArtinMatthews
