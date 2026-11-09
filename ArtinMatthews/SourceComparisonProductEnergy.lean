module

public import ArtinMatthews.SourceComparisonPositiveDyadEnergy
public import ArtinMatthews.SourceComparisonRemovedProducts


set_option backward.privateInPublic true
@[expose] public section

/-! Exact summation of the smoothly cut product boxes. -/

namespace ArtinMatthews

open Finset Filter MeasureTheory
open scoped Topology

noncomputable section

def sourceComparisonProductMellin {q : ℕ} [NeZero q] (h : ZMod q)
    (S G R : Finset ℕ) (β : ℕ → ℂ) (ψ : ℝ → ℂ) (Y t : ℝ) : ℂ :=
  sourceComparisonCutTriple (S×ˢ(G×ˢR)) (sourceComparisonProductCoefficient h β) ψ Y Y t

theorem sourceComparisonProductMellin_eq_dyads {q : ℕ} [NeZero q] (h : ZMod q)
    (S G R : Finset ℕ) (β : ℕ → ℂ) (ψ : ℝ → ℂ) (a b Y t : ℝ)
    (hY : 0 < Y) (hψ : Function.support ψ ⊆ Set.Icc a b)
    (hS : ∀ p ∈ S, 0 < p) (hG : ∀ m ∈ G, 0 < m) (hR : ∀ n ∈ R, 0 < n) :
    sourceComparisonProductMellin h S G R β ψ Y t =
      ∑ j ∈ sourceComparisonOccupiedDyads S G R a b Y,
        sourceComparisonCutTriple (sourceComparisonProductBox S G R j)
          (sourceComparisonProductCoefficient h β) ψ Y Y t := by
  let c (v : ℕ × ℕ × ℕ) :=
    sourceComparisonProductCoefficient h β v*markedPrimePhase (sourceComparisonTriplePosition v) t
  have he (v : ℕ × ℕ × ℕ) :
      sourceComparisonProductCoefficient h β v*ψ ((sourceComparisonTriplePosition v:ℝ)/Y)*
        markedPrimePhase (sourceComparisonTriplePosition v) t =
        c v*ψ ((sourceComparisonTriplePosition v:ℝ)/Y) := by dsimp [c]; ring
  simp only [sourceComparisonProductMellin, sourceComparisonCutTriple, he]
  rw [← sum_div, sourceComparison_cutoff_product_dyads S G R ψ c a b Y hY hψ hS hG hR]

/-- Each collection of occupied product boxes has a fixed cubic logarithmic
count. The estimate is independent of the coefficient vector. -/
theorem sourceComparisonOccupiedDyads_log_card
    (X : ℝ) (hX : 1 ≤ X) (S G R : Finset ℕ) (a b Y : ℝ)
    (hS : ∀ p ∈ S, (p:ℝ) ≤ Real.exp (3*X))
    (hG : ∀ m ∈ G, (m:ℝ) ≤ Real.exp (3*X))
    (hR : ∀ n ∈ R, (n:ℝ) ≤ Real.exp (3*X)) :
    ((sourceComparisonOccupiedDyads S G R a b Y).card:ℝ) ≤
      (1+(Real.log 2+3)/Real.log 2)^3*X^3 := by
  let K := 1+(Real.log 2+3)/Real.log 2
  have hL2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hZ1 : 1 ≤ Real.exp (3*X) := Real.one_le_exp (by positivity)
  have hlog : Real.log (Real.exp (3*X)+1) ≤ Real.log 2+3*X := by
    calc
      _ ≤ Real.log (2*Real.exp (3*X)) := Real.log_le_log (by positivity) (by linarith)
      _ = _ := by rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
  have hset (D : Finset ℕ) (hD : ∀ n ∈ D, (n:ℝ) ≤ Real.exp (3*X)) :
      ((sourceComparisonDyadIndices D).card:ℝ) ≤ K*X := by
    apply (sourceComparisonDyadIndices_card D (Real.exp (3*X)) hZ1 hD).trans
    calc
      _ ≤ 1+(Real.log 2+3*X)/Real.log 2 :=
        add_le_add_right (div_le_div_of_nonneg_right hlog hL2.le) 1
      _ ≤ X+((Real.log 2+3)*X)/Real.log 2 := add_le_add hX
        (div_le_div_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_left hX hL2.le]) hL2.le)
      _ = K*X := by dsimp [K]; ring
  have hc : ((sourceComparisonOccupiedDyads S G R a b Y).card:ℝ) ≤
      ((sourceComparisonDyadIndices S).card:ℝ)*((sourceComparisonDyadIndices G).card:ℝ)*
        ((sourceComparisonDyadIndices R).card:ℝ) := by
    exact_mod_cast sourceComparisonOccupiedDyads_card_le S G R a b Y
  calc
    _ ≤ (K*X)*(K*X)*(K*X) := hc.trans (by gcongr <;> exact hset _ (by assumption))
    _ = _ := by dsimp [K]; ring

theorem sourceComparisonProductMellin_energy_from_boxes {q : ℕ} [NeZero q] (h : ZMod q)
    (S G R : Finset ℕ) (β : ℕ → ℂ) (ψ : ℝ → ℂ) (a b Y T B σ : ℝ)
    (hY : 0 < Y) (hψ : Function.support ψ ⊆ Set.Icc a b)
    (hS : ∀ p ∈ S, 0 < p) (hG : ∀ m ∈ G, 0 < m) (hR : ∀ n ∈ R, 0 < n)
    (E : ℝ) (he : ∀ j ∈ sourceComparisonOccupiedDyads S G R a b Y,
      (∫ t in sourceComparisonHighTimes T B, ‖sourceComparisonCutTriple
        (sourceComparisonProductBox S G R j) (sourceComparisonProductCoefficient h β)
        ψ Y Y (t+σ)‖^2) ≤ E) :
    (∫ t in sourceComparisonHighTimes T B,
      ‖sourceComparisonProductMellin h S G R β ψ Y (t+σ)‖^2) ≤
      ((sourceComparisonOccupiedDyads S G R a b Y).card:ℝ)^2*E := by
  simp_rw [sourceComparisonProductMellin_eq_dyads h S G R β ψ a b Y _ hY hψ hS hG hR]
  exact sourceComparison_finiteSum_energy (sourceComparisonOccupiedDyads S G R a b Y)
    (fun j t => sourceComparisonCutTriple (sourceComparisonProductBox S G R j)
      (sourceComparisonProductCoefficient h β) ψ Y Y (t+σ))
    (fun _ ht => ht.1)
    (fun _ _ => (sourceComparisonCutTriple_continuous _ _ _ _ _).comp
      (continuous_id.add continuous_const)) he

end
end ArtinMatthews
