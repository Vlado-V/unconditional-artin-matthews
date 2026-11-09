module

public import ArtinMatthews.GiantComparisonCircleTransfer
public import ArtinMatthews.GiantComparisonArcBudget


set_option backward.privateInPublic true
@[expose] public section

/-! The comparison shift saves any fixed log power once the actual
centered endpoint has its retained Mellin energy bound. -/
namespace ArtinMatthews
open Filter Finset MeasureTheory
open scoped BigOperators
noncomputable section

private theorem comparison_rpow_sq {L : ℝ} (hL : 0 ≤ L) (t : ℝ) :
    (L^t)^2 = L^(2*t) := by
  rw [← Real.rpow_two, ← Real.rpow_mul hL]
  congr 1
  ring

private theorem comparison_shift_exponent_budget {L Y D A a u v : ℝ} (hL : 2 ≤ L)
    (hY : 0 < Y) (hu : 0 ≤ u) (hv : 0 ≤ v) (huY : u ≤ Y*L^D) (hvY : v ≤ Y*L^D) :
    L^(-(A+D+1))*Real.sqrt (u*v) +
        Real.sqrt (v*(4*(L^a)^2*(Y*L^(-(2*a+D+2*A+4))))) ≤ Y*L^(-A) := by
  have hLp : 0 < L := by linarith
  have hD0 : 0 ≤ L^D := Real.rpow_nonneg hLp.le _
  have hA0 : 0 ≤ L^(-A) := Real.rpow_nonneg hLp.le _
  have hB0 : 0 ≤ L^(-(2*a+D+2*A+4)) := Real.rpow_nonneg hLp.le _
  have hs1 : Real.sqrt (u*v) ≤ Y*L^D := by
    refine (Real.sqrt_le_sqrt (mul_le_mul huY hvY hv (mul_nonneg hY.le hD0))).trans_eq ?_
    rw [← sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg hY.le hD0)]
  have hprod : L^D * L^(2*a) * L^(-(2*a+D+2*A+4)) = L^(-2*(A+2)) := by
    rw [← Real.rpow_add hLp, ← Real.rpow_add hLp]
    congr 1
    ring
  have he : (Y*L^D)*(4*(L^a)^2*(Y*L^(-(2*a+D+2*A+4)))) = (2*Y*L^(-(A+2)))^2 := by
    rw [comparison_rpow_sq hLp.le]
    calc
      _ = 4*Y^2*(L^D*L^(2*a)*L^(-(2*a+D+2*A+4))) := by ring
      _ = _ := by
        rw [hprod, show -2*(A+2) = 2*(-(A+2)) by ring, ← comparison_rpow_sq hLp.le]
        ring
  have hs2 : Real.sqrt (v*(4*(L^a)^2*(Y*L^(-(2*a+D+2*A+4))))) ≤
      2*Y*L^(-(A+2)) := by
    refine (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hvY (by positivity))).trans_eq ?_
    rw [he, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have hminor :
      L^(-(A+D+1))*(Y*L^D) = L⁻¹*(Y*L^(-A)) := by
    rw [show L^(-(A+D+1))*(Y*L^D) = Y*(L^(-(A+D+1))*L^D) by ring,
      ← Real.rpow_add hLp, show -(A+D+1)+D = -A+(-1) by ring,
      Real.rpow_add hLp, Real.rpow_neg_one]
    ring
  have hmajor : 2*Y*L^(-(A+2)) = (2*(L^2)⁻¹)*(Y*L^(-A)) := by
    have hpow : L^(-2 : ℝ) = (L^2)⁻¹ := by
      rw [Real.rpow_neg hLp.le, Real.rpow_two]
    rw [show -(A+2)=-A+(-2) by ring, Real.rpow_add hLp, hpow]
    ring
  have h1 : L⁻¹ ≤ (1/2 : ℝ) := by
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hL
  have h2 : 2*(L^2)⁻¹ ≤ (1/2 : ℝ) := by
    have h := inv_anti₀ (by norm_num : (0 : ℝ) < 4)
      (show 4 ≤ L^2 by nlinarith)
    linarith
  calc
    _ ≤ L^(-(A+D+1))*(Y*L^D) + 2*Y*L^(-(A+2)) :=
      add_le_add (mul_le_mul_of_nonneg_left hs1 (Real.rpow_nonneg hLp.le _)) hs2
    _ ≤ (1/2 : ℝ)*(Y*L^(-A)) + (1/2 : ℝ)*(Y*L^(-A)) := by
      rw [hminor, hmajor]
      exact add_le_add (mul_le_mul_of_nonneg_right h1 (mul_nonneg hY.le hA0))
        (mul_le_mul_of_nonneg_right h2 (mul_nonneg hY.le hA0))
    _ = _ := by ring

theorem giantComparisonNatShiftSum_log_saving (m : ℕ) (C₀ v₀ c d lo hi D A : ℝ)
    (hC₀ : 0 ≤ C₀) (hv₀ : 0 < v₀) (hc : 0 < c) (hd : 0 ≤ d)
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (hD : 0 ≤ D) (hA : 0 ≤ A) :
    let a := giantComparisonArcExponent m C₀ v₀ d (A+D+1)
    let B := 2*a+D+2*A+4
    ∀ᶠ L : ℝ in atTop, ∀ {G : Type} [Fintype G] [DecidableEq G],
      ∀ (P : G → Finset ℕ), (∀ i p, p ∈ P i → p.Prime) →
      Pairwise (fun i j => Disjoint (P i) (P j)) →
      (∀ i, v₀ ≤ bandReciprocalMass (P i)) →
      (Fintype.card G : ℝ) ≤ C₀*Real.log L →
      ∀ {k : ℕ} (A' B' : Finset (G × Fin k)),
      (∀ i, (idealResidualFreeSlots A' i).card ≤ m) →
      (∀ i, (idealResidualFreeSlots B' i).card ≤ m) →
      ∀ U V : ℕ, 0 < U → 0 < V →
      Real.exp (L^c)/4 ≤ (U : ℝ) → Real.exp (L^c)/4 ≤ (V : ℝ) →
      Real.log ((4*U : ℕ) : ℝ) ≤ L^(d+2) → Real.log ((4*V : ℕ) : ℝ) ≤ L^(d+2) →
      ∀ (f : IdealSelectedLabels (idealResidualBands P A') → ℂ)
        (g : IdealSelectedLabels (idealResidualBands P B') → ℂ),
      (∀ x, ‖f x‖ ≤ 1) → (∀ y, ‖g y‖ ≤ 1) →
      (∀ x, idealSelectedProduct x ∉ Ico U (U+4*U) → f x = 0) →
      (∀ y, idealSelectedProduct y ∉ Ico V (V+4*V) → g y = 0) →
      ∀ (S T : Finset ℕ) (F G' : ℕ → ℂ) (Y : ℝ), 0 < Y →
      let Q := L^a
      let H := ((U : ℝ)*(V : ℝ))/Q
      1 ≤ Q → 1 ≤ H → H ≤ Y →
      (∀ w ∈ S, (w : ℝ) ∈ Set.Icc (lo*Y) (hi*Y)) →
      (∑ w ∈ S, ‖F w‖^2) ≤ Y*L^D → (∑ w ∈ T, ‖G' w‖^2) ≤ Y*L^D →
      (∀ r : ℚ, (r.den : ℝ) ≤ Q →
        (∫ t in Set.Icc (-(L*(Y/H))) (L*(Y/H)),
          ‖(Y : ℂ)⁻¹ * giantComparisonMellinPolynomial S (giantComparisonArcTwist (r : ℝ) F) t‖^2) ≤
            L^(-(B+2))) →
      ‖giantComparisonNatShiftSum (idealResidualBands P A') (idealResidualBands P B') f g S T F G'‖ ≤
        Y*L^(-A) := by
  intro a B
  have hE : 0 ≤ A+D+1 := by linarith
  have ha : 0 ≤ a := by
    dsimp only [a, giantComparisonArcExponent, idealMinorCutoffExponent, idealGroupedBudgetExponent]
    have hf : 0 ≤ Real.log (m.factorial : ℝ) := Real.log_nonneg (by exact_mod_cast Nat.factorial_pos m)
    have hi : 0 ≤ Real.log (max 1 v₀⁻¹) := Real.log_nonneg (le_max_left _ _)
    have hk := mul_nonneg hC₀ (add_nonneg hf (mul_nonneg (Nat.cast_nonneg m) hi))
    linarith
  have hB : 0 ≤ B := by dsimp [B]; linarith
  filter_upwards [giantComparisonMultiplier_minor_eventually m C₀ v₀ c d (A+D+1)
    hC₀ hv₀ hc hd hE, giantComparisonNatFourier_arc_log_bound lo hi D B hlo hlohi hD hB,
    eventually_ge_atTop (2 : ℝ)] with L hminor harc hL
  have hLp : 0 < L := by linarith
  intro G _ _ P hP hdis hV hcard k A' B' hA' hB' U V hU hV' hUlo hVlo hUlog hVlog
    f g hf hg hfs hgs S T F G' Y hY Q H hQ hH hHY hS hF hG hcore
  have hρ : H⁻¹ = Q/((U : ℝ)*(V : ℝ)) := by dsimp only [H]; rw [inv_div]
  have hv (i : G) : 0 < bandReciprocalMass (P i) := hv₀.trans_le (hV i)
  have hM (t : ℝ) (_ : t ∈ Set.Ioc (0 : ℝ) 1) (ht : ¬MarkedInRationalArc t Q H⁻¹) :
      ‖giantComparisonMultiplier (idealResidualBands P A') (idealResidualBands P B') f g (-t)‖ ≤
        L^(-(A+D+1)) := by
    have hneg : ¬MarkedInRationalArc (-t) Q (Q/((U : ℝ)*(V : ℝ))) := by
      rw [← hρ, markedInRationalArc_neg_iff]
      exact ht
    exact hminor P hP hdis hV hcard A' B' hA' hB' U V hU hV' hUlo hVlo hUlog hVlog
      f g hf hg hfs hgs (-t) hneg
  have hArc (r : ℚ) (hr : (r.den : ℝ) ≤ Q) :=
    harc S F (r : ℝ) Y H hY hH hHY hS hF (hcore r hr)
  have hb := giantComparisonNatShiftSum_norm_le (idealResidualBands P A') (idealResidualBands P B')
    (fun i => hv i.val.1) (fun i => hv i.val.1) f g hf hg S T F G' hQ
    (inv_le_one_of_one_le₀ hH) (Real.rpow_nonneg hLp.le _)
    (mul_nonneg hY.le (Real.rpow_nonneg hLp.le _)) hM hArc
  refine hb.trans ?_
  exact comparison_shift_exponent_budget hL hY
    (sum_nonneg fun _ _ => sq_nonneg _) (sum_nonneg fun _ _ => sq_nonneg _) hF hG

end
end ArtinMatthews
