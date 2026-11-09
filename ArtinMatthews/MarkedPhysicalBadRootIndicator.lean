module

public import ArtinMatthews.MarkedPhysicalBadRootEstimate


set_option backward.privateInPublic true
@[expose] public section

/-! The actual union of first- and second-bad source roots is dominated
inside the literal positive canonical-root sum, before normalization. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedPhysicalBadRootIndicatorSum
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ)
    (source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
    (d₀ Y : ℝ) {S : ℕ} (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (A B C D : ℝ) (d b a : ℤ) (R Q : ℝ) (ψ : ℝ → ℂ) : ℝ :=
  ∑ p ∈ fixedURootMatrixBoxPoints g₀ A B 0 1 C D true true true true true true,
    ∑ z ∈ markedPhysicalRootTargetWindow d R Y,
      ‖markedBanEdgeKernel ψ Q Y b a (z.2/d)‖ *
        (if |markedMinorIntegerTau ((p.2.1 : ℝ)/(p.1 : ℝ)) z| ≤ 16 ∧
          (((p.2.1 : ℝ)/(p.1 : ℝ)) : AddCircle (1 : ℝ)) ∈
            markedRawBadRootSet e x d₀ Y source then 1 else 0)

theorem markedPhysicalBadRootIndicatorSum_le_kernelSum
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10 : ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
        (d₀ Y : ℝ) (S : ℕ) (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
        (A B C D : ℝ) (d b a : ℤ) (R Q : ℝ) (ψ : ℝ → ℂ),
        markedPhysicalBadRootIndicatorSum e x source d₀ Y g₀ A B C D d b a R Q ψ ≤
          markedPhysicalBadRootKernelSum e x source d₀ Y g₀ A B C D d b a R Q ψ := by
  filter_upwards [markedRawBadRoot_indicator_le_arcs_eventually e he] with x hx
  intro source d₀ Y S g₀ A B C D d b a R Q ψ
  unfold markedPhysicalBadRootIndicatorSum markedPhysicalBadRootKernelSum
  apply Finset.sum_le_sum
  intro p _
  apply Finset.sum_le_sum
  intro z _
  by_cases hs : |markedMinorIntegerTau ((p.2.1 : ℝ)/(p.1 : ℝ)) z| ≤ 16
  · simp only [hs, true_and, ite_true]
    exact mul_le_mul_of_nonneg_left (hx d₀ Y source _) (norm_nonneg _)
  · simp only [hs, false_and, ite_false, mul_zero, le_refl]

theorem markedPhysicalBadRootIndicatorSum_bound
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10 : ℝ) ≤ e j) (hinj : Function.Injective e)
    (β H R T : ℝ) (hβ : 0 ≤ β) (heβ : ∀ j, e j ≤ β)
    (hβhi : β+(1/100 : ℝ) < 1) (hH : 0 ≤ H) (hR : 0 ≤ R)
    {δ : ℝ} (hδ : 0 < δ) (M : ℝ) :
    ∃ E : ℝ, 0 < E ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
        (o : J → Fin (markedPadSlots x)) (d₀ Y Q : ℝ)
        (S : ℕ) (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
        (U V A B C D W : ℝ) (b a : ℤ) (ψ : ℝ → ℂ),
        x^δ ≤ U → x^δ ≤ V → Squarefree S →
        (S : ℝ) ≤ Real.exp (M*(Real.log x)^(49/50 : ℝ)) →
        U ≤ A → A ≤ B → B ≤ 16*U → V ≤ C → C ≤ D → D ≤ 2*V →
        1 ≤ Q → Q ≤ Real.exp (H*(Real.log x)^(1/5 : ℝ)) →
        1 ≤ Y → Y ≤ Real.exp (H*(Real.log x)^(1/5 : ℝ)) →
        Real.exp ((Real.log x)^(1/10 : ℝ)) ≤ Y →
        0 ≤ W → (∀ u, ‖ψ u‖ ≤ W) → (∀ u, ψ u ≠ 0 → |u| ≤ R) →
        markedPhysicalBadRootIndicatorSum e x source d₀ Y g₀ A B C D
          (markedSourceCopiedProduct (markedRawNumericActive source) o) b a R Q ψ / (U*V) ≤
          (16/((riemannZeta 2).re*
            (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))) *
            ((33*W*(8*R+5))*Q^3) * (Real.log x)^(-T) +
            (5*E*W)*x^(-δ/2000) := by
  obtain ⟨E,hE,hbound⟩ := markedPhysicalBadRootKernelSum_bound e he hinj β H R T
    hβ heβ hβhi hH hR hδ M
  refine ⟨E,hE,?_⟩
  filter_upwards [hbound, markedPhysicalBadRootIndicatorSum_le_kernelSum e he,
    eventually_gt_atTop (0 : ℝ)] with x hx hdom hx0
  intro source o d₀ Y Q S g₀ U V A B C D W b a ψ hU hV hS hSr
    hUA hAB hB hVC hCD hD hQ hQhi hY hYhi hYlo hW hψ hsupp
  have hUp : 0 < U := (Real.rpow_pos_of_pos hx0 δ).trans_le hU
  have hVp : 0 < V := (Real.rpow_pos_of_pos hx0 δ).trans_le hV
  apply (div_le_div_of_nonneg_right (hdom source d₀ Y S g₀ A B C D
    (markedSourceCopiedProduct (markedRawNumericActive source) o) b a R Q ψ)
      (mul_pos hUp hVp).le).trans
  exact hx source o d₀ Y Q S g₀ U V A B C D W b a ψ hU hV hS hSr
    hUA hAB hB hVC hCD hD hQ hQhi hY hYhi hYlo hW hψ hsupp

end ArtinMatthews
