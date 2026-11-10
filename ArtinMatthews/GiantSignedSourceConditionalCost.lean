module

public import ArtinMatthews.GiantSignedBirthPivots
public import ArtinMatthews.GiantSignedBirthMixedBoundary
public import ArtinMatthews.GiantSignedSourceVisitEnergy
public import ArtinMatthews.GiantSignedEdgeSlotBudget
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

/-! The literal costs of the conditional initial, ghost and edge rows.
Their product pays the exact rank, with an exponent independent of the
copied slot count. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.decEq

def giantSignedSourceConditionalEdgeExponent (C₀ C₁ BS ρ v vmin : ℝ) (tmax : ℕ) : ℝ :=
  C₁ + C₀ * Real.log (max 1 BS) + C₀ * Real.log
    (max 1 (giantSignedEdgeUniformConstant ρ v vmin⁻¹ 2 tmax))

def giantSignedSourceHighRankCostExponent (C₀ C₁ BS ρ v vmin vmax : ℝ) (tmax : ℕ) : ℝ :=
  1 + giantSignedSourceVisitExponent C₀ vmax ρ v +
    giantSignedSourceConditionalEdgeExponent C₀ C₁ BS ρ v vmin tmax

theorem giantSignedSourceConditionalEdgeExponent_nonneg {C₀ C₁ BS ρ v vmin : ℝ} (tmax : ℕ)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) :
    0 ≤ giantSignedSourceConditionalEdgeExponent C₀ C₁ BS ρ v vmin tmax :=
  add_nonneg (add_nonneg hC₁ (mul_nonneg hC₀ (Real.log_nonneg (le_max_left _ _))))
    (mul_nonneg hC₀ (Real.log_nonneg (le_max_left _ _)))

theorem giantSignedSourceHighRankCostExponent_nonneg {C₀ C₁ BS ρ v vmin vmax : ℝ} (tmax : ℕ)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hvmax : 0 ≤ vmax) (hρ : 0 < ρ) (hv : 0 ≤ v) :
    0 ≤ giantSignedSourceHighRankCostExponent C₀ C₁ BS ρ v vmin vmax tmax := by
  have hvisit : 0 ≤ giantSignedSourceVisitExponent C₀ vmax ρ v := by
    unfold giantSignedSourceVisitExponent
    positivity
  exact add_nonneg (add_nonneg zero_le_one hvisit)
    (giantSignedSourceConditionalEdgeExponent_nonneg tmax hC₀ hC₁)

private theorem fixed_cost_pow_le {L C₀ a : ℝ} {j : ℕ}
    (hL : 0 < L) (ha : 0 ≤ a) (hj : (j : ℝ) ≤ C₀*Real.log L) :
    a^j ≤ L^(C₀*Real.log (max 1 a)) := by
  let b := max 1 a
  have hb : 1 ≤ b := le_max_left _ _
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  calc
    _ ≤ b^j := pow_le_pow_left₀ ha (le_max_right _ _) _
    _ = Real.exp (Real.log b * (j : ℝ)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hb0]
    _ ≤ Real.exp (Real.log L * (C₀*Real.log b)) := by
      apply Real.exp_le_exp.mpr
      calc
        _ = (j : ℝ)*Real.log b := mul_comm _ _
        _ ≤ (C₀*Real.log L)*Real.log b := mul_le_mul_of_nonneg_right hj (Real.log_nonneg hb)
        _ = _ := by ring
    _ = _ := (Real.rpow_def_of_pos hL _).symm

private theorem operation_prod {R : Type*} [CommMonoid R] {n : ℕ}
    (f : GiantSignedBirthOperation n → R) :
    (∏ o, f o) = f .initial * (∏ i : Fin (n+1), f (.visit i)) *
      (∏ i : Fin n, f (.edge i)) := by
  let e : (Unit ⊕ (Fin n ⊕ Fin (n+1))) ≃ GiantSignedBirthOperation n :=
    { toFun := fun
        | .inl _ => .initial
        | .inr (.inl i) => .edge i
        | .inr (.inr i) => .visit i
      invFun := fun
        | .initial => .inl ()
        | .edge i => .inr (.inl i)
        | .visit i => .inr (.inr i)
      left_inv := by
        rintro (a | i | i)
        · cases a; rfl
        · rfl
        · rfl
      right_inv := by intro o; cases o <;> rfl }
  rw [← e.prod_comp f, Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_unique]
  change f .initial * ((∏ i : Fin n, f (.edge i)) * ∏ i : Fin (n+1), f (.visit i)) = _
  ac_rfl

theorem giantSignedSourceConditionalCosts_le {S B I : Type*} [Fintype S] [Fintype B]
    {n M H : ℕ} (patterns : Fin n → Finset I) (V : B → ℝ) (visitQ : Fin (n+1) → ℝ)
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B M n H)) (tmax : ℕ)
    {L C₀ C₁ BS ρ v vmin vmax W mass Δ : ℝ} (hL : 2 ≤ L)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hBS : 0 ≤ BS) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hv : 0 ≤ v) (hvmax : 0 ≤ vmax) (hW : 0 ≤ W) (hΔ : 0 ≤ Δ)
    (hmass : 0 ≤ mass) (hmass2 : mass ≤ 2) (hinit : mass^(Fintype.card B*M) ≤ 2)
    (hV0 : ∀ g, 0 ≤ V g) (hVmax : ∀ g, V g ≤ vmax)
    (hQ0 : ∀ i, 0 ≤ visitQ i) (hQ1 : ∀ i, visitQ i ≤ 1)
    (hS : (Fintype.card S : ℝ) ≤ C₀*Real.log L)
    (hB : (Fintype.card B : ℝ) ≤ C₀*Real.log L)
    (hcost : ∀ i, ((patterns i).card : ℝ)*W ≤ L^C₁) :
    let birth (o : GiantSignedBirthOperation n) := Δ^(giantSignedUniformBirthStageNonpivots σ o).card
    (birth .initial * mass^(Fintype.card B*M)) *
      (∏ i : Fin (n+1), birth (.visit i) *
        ∏ g, Real.exp (‖((-(1-visitQ i)*V g/ρ : ℝ) : ℂ)‖*mass*v)) *
      (∏ i : Fin n, birth (.edge i) * (((patterns i).card : ℝ)*W *
        (giantSignedEdgeUniformConstant ρ v vmin⁻¹ mass tmax)^Fintype.card B *
        BS^Fintype.card S)) ≤
      (L^giantSignedSourceHighRankCostExponent C₀ C₁ BS ρ v vmin vmax tmax)^(n+1) *
        Δ^giantSignedUniformBirthRank σ := by
  let U (a : ℝ) := giantSignedEdgeUniformConstant ρ v vmin⁻¹ a tmax
  let Cv := giantSignedSourceVisitExponent C₀ vmax ρ v
  let Ce := giantSignedSourceConditionalEdgeExponent C₀ C₁ BS ρ v vmin tmax
  let Ch := giantSignedSourceHighRankCostExponent C₀ C₁ BS ρ v vmin vmax tmax
  let G (i : Fin (n+1)) := ∏ g, Real.exp (‖((-(1-visitQ i)*V g/ρ : ℝ) : ℂ)‖*mass*v)
  let E (i : Fin n) := ((patterns i).card : ℝ)*W * (U mass)^Fintype.card B * BS^Fintype.card S
  let a (o : GiantSignedBirthOperation n) := Δ^(giantSignedUniformBirthStageNonpivots σ o).card
  have hL1 : 1 ≤ L := (by norm_num : (1 : ℝ) ≤ 2).trans hL
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hCe : 0 ≤ Ce := giantSignedSourceConditionalEdgeExponent_nonneg tmax hC₀ hC₁
  have hU0 (u : ℝ) : 0 ≤ U u := giantSignedEdgeUniformConstant_nonneg hρ1 hv
  have hU2 : U mass ≤ U 2 := by
    unfold U giantSignedEdgeUniformConstant
    have hd : 0 < 1-ρ := sub_pos.mpr hρ1
    gcongr
  have hG (i : Fin (n+1)) : G i ≤ L^Cv := by
    let R := (vmax+1)/ρ*2*v
    have hR : 0 ≤ R := by dsimp only [R]; positivity
    have harg (g : B) : ‖((-(1-visitQ i)*V g/ρ : ℝ) : ℂ)‖*mass*v ≤ R := by
      have hlabel : ‖((-(1-visitQ i)*V g/ρ : ℝ) : ℂ)‖ ≤ (vmax+1)/ρ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_neg,
          abs_of_nonneg (sub_nonneg.mpr (hQ1 i)), abs_of_nonneg (hV0 g), abs_of_pos hρ]
        apply div_le_div_of_nonneg_right _ hρ.le
        exact (mul_le_of_le_one_left (hV0 g) (by linarith [hQ0 i])).trans
          ((hVmax g).trans (by linarith))
      exact mul_le_mul_of_nonneg_right (mul_le_mul hlabel hmass2 hmass (by positivity)) hv
    change (∏ g, _) ≤ L^Cv
    rw [← Real.exp_sum, Real.rpow_def_of_pos hL0]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ ∑ _g : B, R := Finset.sum_le_sum (fun g _ => harg g)
      _ = (Fintype.card B : ℝ)*R := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ (C₀*Real.log L)*R := mul_le_mul_of_nonneg_right hB hR
      _ = _ := by unfold Cv giantSignedSourceVisitExponent R; ring
  have hE0 (i : Fin n) : 0 ≤ E i :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hW) (pow_nonneg (hU0 mass) _))
      (pow_nonneg hBS _)
  have hE (i : Fin n) : E i ≤ L^Ce := by
    have hb : (U mass)^Fintype.card B ≤ L^(C₀*Real.log (max 1 (U 2))) :=
      (pow_le_pow_left₀ (hU0 mass) hU2 _).trans (fixed_cost_pow_le hL0 (hU0 2) hB)
    have hs := fixed_cost_pow_le hL0 hBS hS
    calc
      _ ≤ L^C₁ * L^(C₀*Real.log (max 1 (U 2))) * L^(C₀*Real.log (max 1 BS)) :=
        mul_le_mul (mul_le_mul (hcost i) hb (pow_nonneg (hU0 mass) _)
          (Real.rpow_nonneg hL0.le _)) hs (pow_nonneg hBS _) (by positivity)
      _ = _ := by
        rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
        congr 1
        unfold Ce U giantSignedSourceConditionalEdgeExponent
        ring
  have hTwo : 2 ≤ L^(n+1) := hL.trans (by
    simpa only [pow_one] using (pow_le_pow_right₀ hL1 (Nat.succ_le_succ (Nat.zero_le n)) :
      L^(1 : ℕ) ≤ L^(n+1)))
  have hbase : mass^(Fintype.card B*M) * (∏ i, G i) * (∏ i, E i) ≤ (L^Ch)^(n+1) := by
    have hg : (∏ i, G i) ≤ (L^Cv)^(n+1) := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (Finset.prod_le_prod₀ (s := Finset.univ) (fun i _ => by unfold G; positivity) (fun i _ => hG i))
    have he : (∏ i, E i) ≤ (L^Ce)^(n+1) := by
      have h' : (∏ i, E i) ≤ (L^Ce)^n := by
        simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
          (Finset.prod_le_prod₀ (s := Finset.univ) (fun i _ => hE0 i) (fun i _ => hE i))
      exact h'.trans (pow_le_pow_right₀ (Real.one_le_rpow hL1 hCe) (Nat.le_succ n))
    calc
      _ ≤ L^(n+1) * (L^Cv)^(n+1) * (L^Ce)^(n+1) :=
        mul_le_mul (mul_le_mul (hinit.trans hTwo) hg (by unfold G; positivity)
          (pow_nonneg hL0.le _)) he (Finset.prod_nonneg (fun i _ => hE0 i)) (by positivity)
      _ = _ := by
        rw [← mul_pow, ← mul_pow]
        congr 1
        calc
          L * L^Cv * L^Ce = L^(1 : ℝ) * L^Cv * L^Ce := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]; rfl
  have ha : a .initial * (∏ i : Fin (n+1), a (.visit i)) * (∏ i : Fin n, a (.edge i)) =
      Δ^giantSignedUniformBirthRank σ := by
    rw [← operation_prod a]
    exact giantSignedUniformBirthStageNonpivots_atom_product σ Δ
  change (a .initial * mass^(Fintype.card B*M)) * (∏ i, a (.visit i) * G i) *
    (∏ i, a (.edge i) * E i) ≤ (L^Ch)^(n+1) * Δ^giantSignedUniformBirthRank σ
  calc
    _ = (mass^(Fintype.card B*M) * (∏ i, G i) * (∏ i, E i)) *
        (a .initial * (∏ i : Fin (n+1), a (.visit i)) * (∏ i : Fin n, a (.edge i))) := by
      simp only [Finset.prod_mul_distrib]
      ac_rfl
    _ ≤ _ := by rw [ha]; exact mul_le_mul_of_nonneg_right hbase (pow_nonneg hΔ _)

end
end ArtinMatthews
