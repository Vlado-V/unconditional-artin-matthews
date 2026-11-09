module

public import ArtinMatthews.MarkedPhysicalBadRootIndicator


set_option backward.privateInPublic true
@[expose] public section

/-! With the actual logarithmic detector height, the canonical-root bad
indicator sum has an arbitrarily strong logarithmic saving. The broad
subexponential height bound is used only for the arithmetic error. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysicalRoot_log_cube_cancel {L Q G A₀ : ℝ}
    (hL : 0 < L) (hQ₀ : 0 ≤ Q) (hQ : Q ≤ L^A₀) :
    Q^3 * L^(-(G+3*A₀)) ≤ L^(-G) := by
  have hcube : L^(A₀*3) = (L^A₀)^3 := by
    simpa only [Nat.cast_ofNat] using Real.rpow_mul_natCast hL.le A₀ 3
  calc
    _ ≤ (L^A₀)^3 * L^(-(G+3*A₀)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hQ₀ hQ 3) (Real.rpow_nonneg hL.le _)
    _ = L^(A₀*3) * L^(-(G+3*A₀)) := by
      rw [hcube]
    _ = L^(A₀*3 + -(G+3*A₀)) := (Real.rpow_add hL _ _).symm
    _ = _ := by congr 1; ring

theorem markedPhysicalBadRootIndicatorSum_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10 : ℝ) ≤ e j) (hinj : Function.Injective e)
    (β H R A₀ G : ℝ) (hβ : 0 ≤ β) (heβ : ∀ j, e j ≤ β)
    (hβhi : β+(1/100 : ℝ) < 1) (hH : 0 ≤ H) (hR : 0 ≤ R)
    {δ : ℝ} (hδ : 0 < δ) (M : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
        (o : J → Fin (markedPadSlots x)) (d₀ Y Q : ℝ)
        (S : ℕ) (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
        (U V A B C D W : ℝ) (b a : ℤ) (ψ : ℝ → ℂ),
        x^δ ≤ U → x^δ ≤ V → Squarefree S →
        (S : ℝ) ≤ Real.exp (M*(Real.log x)^(49/50 : ℝ)) →
        U ≤ A → A ≤ B → B ≤ 16*U → V ≤ C → C ≤ D → D ≤ 2*V →
        1 ≤ Q → Q ≤ Real.exp (H*(Real.log x)^(1/5 : ℝ)) →
        Q ≤ (Real.log x)^A₀ →
        1 ≤ Y → Y ≤ Real.exp (H*(Real.log x)^(1/5 : ℝ)) →
        Real.exp ((Real.log x)^(1/10 : ℝ)) ≤ Y →
        0 ≤ W → (∀ u, ‖ψ u‖ ≤ W) → (∀ u, ψ u ≠ 0 → |u| ≤ R) →
        markedPhysicalBadRootIndicatorSum e x source d₀ Y g₀ A B C D
          (markedSourceCopiedProduct (markedRawNumericActive source) o) b a R Q ψ / (U*V) ≤
          ((16/((riemannZeta 2).re*
            (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))) *
            (33*(8*R+5)) + 1) * W * (Real.log x)^(-G) := by
  obtain ⟨E,hE,hbound⟩ := markedPhysicalBadRootIndicatorSum_bound e he hinj β H R (G+3*A₀)
    hβ heβ hβhi hH hR hδ M
  have herr := (markedPhysicalBadRoot_error_scale_isLittleO E 1 G hδ).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hbound, herr, eventually_gt_atTop (1 : ℝ)] with x hx herrx hx1
  intro source o d₀ Y Q S g₀ U V A B C D W b a ψ hU hV hS hSr
    hUA hAB hB hVC hCD hD hQ hQhi hQlog hY hYhi hYlo hW hψ hsupp
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have he : (5*E)*x^(-δ/2000) ≤ (Real.log x)^(-G) := by
    have hleft : 0 ≤ (5*E)*x^(-δ/2000) := by positivity
    have hright : 0 ≤ (Real.log x)^(-G) := Real.rpow_nonneg hlog.le _
    simpa only [mul_one, one_mul, Real.norm_eq_abs, abs_of_nonneg hleft,
      abs_of_nonneg hright] using herrx
  have hpow := markedPhysicalRoot_log_cube_cancel (G := G) hlog (zero_le_one.trans hQ) hQlog
  have hden : 0 ≤ 16/((riemannZeta 2).re*
      (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ)) := by
    have hd := (fixedURoot_normalized_density_bounds hS).1
    simpa only [div_eq_mul_inv, one_mul] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) hd
  apply (hx source o d₀ Y Q S g₀ U V A B C D W b a ψ hU hV hS hSr
    hUA hAB hB hVC hCD hD hQ hQhi hY hYhi hYlo hW hψ hsupp).trans
  calc
    _ = ((16/((riemannZeta 2).re*
          (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))) *
          (33*(8*R+5))*W) * (Q^3 * (Real.log x)^(-(G+3*A₀))) +
          W*((5*E)*x^(-δ/2000)) := by ring
    _ ≤ ((16/((riemannZeta 2).re*
          (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))) *
          (33*(8*R+5))*W) * (Real.log x)^(-G) + W*(Real.log x)^(-G) :=
      add_le_add (mul_le_mul_of_nonneg_left hpow (by positivity))
        (mul_le_mul_of_nonneg_left he hW)
    _ = _ := by ring

end ArtinMatthews
