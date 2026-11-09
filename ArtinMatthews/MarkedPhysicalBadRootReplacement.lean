module

public import ArtinMatthews.MarkedPhysicalRootPositiveCount
public import ArtinMatthews.MarkedPhysicalRootErrorBudget
public import ArtinMatthews.MarkedPhysicalRootArcSum
public import ArtinMatthews.MarkedRootDiscrepancyAbsorption


set_option backward.privateInPublic true
@[expose] public section

/-! A power-saving replacement for the literal bad-root majorant and
absolute one-edge kernel, with the copied marking divisor retained. The
Haar main term is explicit; its separate logarithmic estimate is not assumed. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators Asymptotics
attribute [local instance] Classical.propDecidable

theorem markedPhysicalBadRoot_discrepancy_power_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10 : ℝ) ≤ e j) (β H R : ℝ)
    (hβ : 0 ≤ β) (heβ : ∀ j, e j ≤ β) (hβhi : β+(1/100 : ℝ) < 1)
    (hH : 0 ≤ H) (hR : 0 ≤ R) {δ : ℝ} (hδ : 0 < δ) (M : ℝ) :
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
        0 ≤ W → (∀ u, ‖ψ u‖ ≤ W) →
        |markedPhysicalRootPositiveDiscrepancy Finset.univ g₀ U V A B C D
          (markedPhysicalBadArcLower e x source d₀ Y)
          (markedPhysicalBadArcUpper e x source d₀ Y)
          (markedPhysicalBadArcCoefficient e x source d₀ Y)
          (markedSourceCopiedProduct (markedRawNumericActive source) o) b a R Y Q ψ| ≤
          (5*E*W)*x^(-δ/2000) := by
  obtain ⟨E,hE,hcount⟩ := markedPhysicalRootPositiveDiscrepancy_bound hδ M
  refine ⟨E,hE,?_⟩
  have hμ := eventually_all.mpr (fun I : Finset J =>
    marked_actual_harmonic_fresh_probability_eventually (fun j : ↥(Finset.univ \ I) => e j.1)
      (fun j => by linarith [he j.1]))
  filter_upwards [hcount,hμ,eventually_gt_atTop (0 : ℝ),
    markedPhysicalRoot_actual_error_budget e he β H R (δ/2000) hβ heβ hβhi hH hR
      (by positivity)] with x hx hμx hx0 hbudget
  intro source o d₀ Y Q S g₀ U V A B C D W b a ψ hU hV hS hSr
    hUA hAB hB hVC hCD hD hQ hQhi hY hYhi hW hψ
  have hm : (∑ i : MarkedPhysicalBadArcIndex e x source d₀ Y,
      |markedPhysicalBadArcCoefficient e x source d₀ Y i|) =
      markedRawBadRootArcComplexity e x d₀ Y source := by
    simp_rw [abs_of_nonneg (markedPhysicalBadArcCoefficient_nonneg e x source d₀ Y
      (fun I => (hμx I).1) _)]
    exact markedPhysicalBadArcCoefficient_sum e x source d₀ Y
  have hc := hx Finset.univ S g₀ U V A B C D
    (markedPhysicalBadArcLower e x source d₀ Y)
    (markedPhysicalBadArcUpper e x source d₀ Y)
    (markedPhysicalBadArcCoefficient e x source d₀ Y)
    (markedSourceCopiedProduct (markedRawNumericActive source) o) b a R Y Q W ψ
    hU hV hS hSr hUA hAB hB hVC hCD hD (fun i _ => markedPhysicalBadArc_bounds e x source d₀ Y i)
    hQ hY hW hψ
  rw [hm] at hc
  calc
    _ ≤ (5*E*W)*x^(-δ/1000)*Q^3*
      ((markedPhysicalRootTargetWindow (markedSourceCopiedProduct (markedRawNumericActive source) o) R Y).card : ℝ)*
      markedRawBadRootArcComplexity e x d₀ Y source := hc
    _ = ((5*E*W)*x^(-δ/1000))*
      (((markedPhysicalRootTargetWindow (markedSourceCopiedProduct (markedRawNumericActive source) o) R Y).card : ℝ)*
        markedRawBadRootArcComplexity e x d₀ Y source*Q^3) := by ring_nf
    _ ≤ ((5*E*W)*x^(-δ/1000))*x^(δ/2000) :=
      mul_le_mul_of_nonneg_left (hbudget source o d₀ Y Q hY hYhi
        (zero_le_one.trans hQ) hQhi) (by positivity)
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add hx0]
      congr 2
      ring_nf

section
variable {J : Type*} [Fintype J] [DecidableEq J]
  (e : J → ℝ) (x : ℝ)
  (source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
  (d₀ Y : ℝ) {S : ℕ} (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
  (A B C D : ℝ) (d b a : ℤ) (R Q : ℝ) (ψ : ℝ → ℂ)

def markedPhysicalBadRootKernelSum : ℝ :=
  ∑ p ∈ fixedURootMatrixBoxPoints g₀ A B 0 1 C D true true true true true true,
    ∑ z ∈ markedPhysicalRootTargetWindow d R Y,
      ‖markedBanEdgeKernel ψ Q Y b a (z.2/d)‖ *
        (if |markedMinorIntegerTau ((p.2.1 : ℝ)/(p.1 : ℝ)) z| ≤ 16 then
          markedRawBadRootArcMajorant e x d₀ Y source
            (((p.2.1 : ℝ)/(p.1 : ℝ)) : AddCircle (1 : ℝ)) else 0)

def markedPhysicalBadRootKernelMain : ℝ :=
  ∑ i : MarkedPhysicalBadArcIndex e x source d₀ Y,
    ∑ z ∈ markedPhysicalRootTargetWindow d R Y,
      markedPhysicalBadArcCoefficient e x source d₀ Y i *
        ‖markedBanEdgeKernel ψ Q Y b a (z.2/d)‖ *
        markedPhysicalRootStripMain S A B
          (markedPhysicalBadArcLower e x source d₀ Y i)
          (markedPhysicalBadArcUpper e x source d₀ Y i) C D z

theorem markedPhysicalBadRootKernel_error_eq (U V : ℝ) (hA : 1 < A)
    (hfirst : Y^(-7/10 : ℝ) < (1/2 : ℝ))
    (hbeta : ∀ j,100*Real.exp (-((Real.log x)^(e j))) < (1/2 : ℝ)) :
    (markedPhysicalBadRootKernelSum e x source d₀ Y g₀ A B C D d b a R Q ψ -
      markedPhysicalBadRootKernelMain e x source d₀ Y (S := S) A B C D d b a R Q ψ)/(U*V) =
      markedPhysicalRootPositiveDiscrepancy Finset.univ g₀ U V A B C D
        (markedPhysicalBadArcLower e x source d₀ Y)
        (markedPhysicalBadArcUpper e x source d₀ Y)
        (markedPhysicalBadArcCoefficient e x source d₀ Y) d b a R Y Q ψ := by
  unfold markedPhysicalBadRootKernelSum
  rw [markedPhysicalBadRootArc_weighted_root_sum e x source d₀ Y g₀ A B C D hA _ _ hfirst hbeta]
  unfold markedPhysicalBadRootKernelMain markedPhysicalRootPositiveDiscrepancy
  rw [Finset.product_eq_sprod, Finset.sum_product, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z _
  ring_nf

end

theorem markedPhysicalBadRootKernel_power_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10 : ℝ) ≤ e j) (β H R : ℝ)
    (hβ : 0 ≤ β) (heβ : ∀ j, e j ≤ β) (hβhi : β+(1/100 : ℝ) < 1)
    (hH : 0 ≤ H) (hR : 0 ≤ R) {δ : ℝ} (hδ : 0 < δ) (M : ℝ) :
    ∃ E : ℝ, 0 < E ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
        (o : J → Fin (markedPadSlots x)) (d₀ Y Q : ℝ)
        (S : ℕ) (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
        (U V A B C D W : ℝ) (b a : ℤ) (ψ : ℝ → ℂ),
        x^δ ≤ U → x^δ ≤ V → Squarefree S →
        (S : ℝ) ≤ Real.exp (M*(Real.log x)^(49/50 : ℝ)) →
        U ≤ A → A ≤ B → B ≤ 16*U → V ≤ C → C ≤ D → D ≤ 2*V →
        1 ≤ Q → Q ≤ Real.exp (H*(Real.log x)^(1/5 : ℝ)) →
        1 ≤ Y → Real.exp ((Real.log x)^(1/10 : ℝ)) ≤ Y →
        Y ≤ Real.exp (H*(Real.log x)^(1/5 : ℝ)) →
        0 ≤ W → (∀ u, ‖ψ u‖ ≤ W) →
        |(markedPhysicalBadRootKernelSum e x source d₀ Y g₀ A B C D
            (markedSourceCopiedProduct (markedRawNumericActive source) o) b a R Q ψ -
          markedPhysicalBadRootKernelMain e x source d₀ Y (S := S) A B C D
            (markedSourceCopiedProduct (markedRawNumericActive source) o) b a R Q ψ)/(U*V)| ≤
          (5*E*W)*x^(-δ/2000) := by
  obtain ⟨E,hE,hd⟩ := markedPhysicalBadRoot_discrepancy_power_saving
    e he β H R hβ heβ hβhi hH hR hδ M
  refine ⟨E,hE,?_⟩
  filter_upwards [hd, markedRootArc_actual_widths_eventually e he,
    eventually_gt_atTop (1 : ℝ)] with x hx hwidth hx1
  intro source o d₀ Y Q S g₀ U V A B C D W b a ψ hU hV hS hSr
    hUA hAB hB hVC hCD hD hQ hQhi hY hYlo hYhi hW hψ
  have hA : 1 < A := ((Real.one_lt_rpow hx1 hδ).trans_le hU).trans_le hUA
  rw [markedPhysicalBadRootKernel_error_eq e x source d₀ Y g₀ A B C D _ b a R Q ψ
    U V hA (hwidth.2 Y hYlo).2 (fun j => (hwidth.1 j).2)]
  exact hx source o d₀ Y Q S g₀ U V A B C D W b a ψ hU hV hS hSr
    hUA hAB hB hVC hCD hD hQ hQhi hY hYhi hW hψ

theorem markedPhysicalBadRoot_error_scale_isLittleO (E W L : ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    (fun x : ℝ => (5*E*W)*x^(-δ/2000)) =o[atTop]
      (fun x : ℝ => (Real.log x)^(-L)) := by
  convert (marked_root_power_isLittleO_log (by positivity : 0 < δ/2000) L).const_mul_left (5*E*W) using 1
  funext x
  congr 1
  ring_nf

end ArtinMatthews
