module

public import ArtinMatthews.MarkedPhysicalRootPositiveCount


set_option backward.privateInPublic true
@[expose] public section

/-! The positive absolute-kernel strip replacement retains an arbitrary
fixed residue/target incidence predicate in both the count and its main term. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedPhysicalRootIncidenceDiscrepancy {ι : Type*} (I : Finset ι)
    {S : ℕ} (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (U V A B C D : ℝ) (α β c : ι → ℝ)
    (d b a : ℤ) (R Y Q : ℝ) (gate : (ℤ × ℤ) → Prop) (ψ : ℝ → ℂ) : ℝ :=
  (∑ iz ∈ I.product (markedPhysicalRootTargetWindow d R Y),
    (if gate iz.2 then c iz.1 * ‖markedBanEdgeKernel ψ Q Y b a (iz.2.2/d)‖ else 0) *
      (((markedPhysicalRootStripPoints g₀ A B (α iz.1) (β iz.1) C D iz.2).card : ℝ) -
        markedPhysicalRootStripMain S A B (α iz.1) (β iz.1) C D iz.2)) / (U*V)

theorem markedPhysicalRootIncidenceDiscrepancy_bound {δ : ℝ} (hδ : 0 < δ) (M : ℝ) :
    ∃ E : ℝ, 0 < E ∧ ∀ᶠ x : ℝ in atTop,
      ∀ {ι : Type*} (I : Finset ι) (S : ℕ) (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
        (U V A B C D : ℝ) (α β c : ι → ℝ)
        (d b a : ℤ) (R Y Q W : ℝ) (gate : (ℤ × ℤ) → Prop) (ψ : ℝ → ℂ),
        x^δ ≤ U → x^δ ≤ V → Squarefree S →
        (S : ℝ) ≤ Real.exp (M*(Real.log x)^(49/50 : ℝ)) →
        U ≤ A → A ≤ B → B ≤ 16*U → V ≤ C → C ≤ D → D ≤ 2*V →
        (∀ i ∈ I, 0 ≤ α i ∧ β i ≤ 1) →
        1 ≤ Q → 1 ≤ Y → 0 ≤ W → (∀ u, ‖ψ u‖ ≤ W) →
        |markedPhysicalRootIncidenceDiscrepancy I g₀ U V A B C D α β c d b a R Y Q gate ψ| ≤
          (5*E*W)*x^(-δ/1000)*Q^3*
            ((markedPhysicalRootTargetWindow d R Y).card : ℝ)*(∑ i ∈ I, |c i|) := by
  obtain ⟨E,hE,hcount⟩ := markedPhysicalRootStrip_sum_error hδ M
  refine ⟨E,hE,?_⟩
  filter_upwards [hcount, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  intro ι I S g₀ U V A B C D α β c d b a R Y Q W gate ψ hU hV hS hSr
    hUA hAB hB hVC hCD hD hα hQ hY hW hψ
  have hUp : 0 < U := (Real.rpow_pos_of_pos hx0 δ).trans_le hU
  have hVp : 0 < V := (Real.rpow_pos_of_pos hx0 δ).trans_le hV
  have hh := hx (I.product (markedPhysicalRootTargetWindow d R Y)) S g₀ U V A B C D
    (fun iz => α iz.1) (fun iz => β iz.1) Prod.snd
    (fun iz => ((if gate iz.2 then c iz.1*‖markedBanEdgeKernel ψ Q Y b a (iz.2.2/d)‖ else 0 : ℝ) : ℂ))
    hU hV hS hSr hUA hAB hB hVC hCD hD
    (fun iz hiz => hα iz.1 (Finset.mem_product.mp hiz).1)
  have hcoeff : (∑ iz ∈ I.product (markedPhysicalRootTargetWindow d R Y),
      ‖((if gate iz.2 then c iz.1*‖markedBanEdgeKernel ψ Q Y b a (iz.2.2/d)‖ else 0 : ℝ) : ℂ)‖) ≤
      5*W*Q^3*((markedPhysicalRootTargetWindow d R Y).card : ℝ)*(∑ i ∈ I, |c i|) := by
    calc
      _ ≤ ∑ iz ∈ I.product (markedPhysicalRootTargetWindow d R Y), |c iz.1| * (5*W*Q^3) := by
        apply Finset.sum_le_sum
        intro iz _
        by_cases he : gate iz.2
        · rw [ite_eq_left he, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg _)]
          exact mul_le_mul_of_nonneg_left (markedBanEdgeKernel_norm_le_five ψ hQ hY hW hψ b a _)
            (abs_nonneg _)
        · rw [ite_eq_right he, Complex.ofReal_zero, norm_zero]
          positivity
      _ = _ := by
        rw [Finset.product_eq_sprod, Finset.sum_product]
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [← Finset.mul_sum, ← Finset.sum_mul]
        ring
  have heq : (∑ iz ∈ I.product (markedPhysicalRootTargetWindow d R Y),
      ((if gate iz.2 then c iz.1*‖markedBanEdgeKernel ψ Q Y b a (iz.2.2/d)‖ else 0 : ℝ) : ℂ) *
        (((markedPhysicalRootStripPoints g₀ A B (α iz.1) (β iz.1) C D iz.2).card : ℂ) -
          (markedPhysicalRootStripMain S A B (α iz.1) (β iz.1) C D iz.2 : ℂ))) =
      ((∑ iz ∈ I.product (markedPhysicalRootTargetWindow d R Y),
        (if gate iz.2 then c iz.1*‖markedBanEdgeKernel ψ Q Y b a (iz.2.2/d)‖ else 0) *
          (((markedPhysicalRootStripPoints g₀ A B (α iz.1) (β iz.1) C D iz.2).card : ℝ) -
            markedPhysicalRootStripMain S A B (α iz.1) (β iz.1) C D iz.2)) : ℝ) := by
    push_cast
    rfl
  rw [heq, Complex.norm_real, Real.norm_eq_abs] at hh
  unfold markedPhysicalRootIncidenceDiscrepancy
  rw [abs_div, abs_of_pos (mul_pos hUp hVp)]
  apply hh.trans
  apply (mul_le_mul_of_nonneg_left hcoeff (by positivity : 0 ≤ E*x^(-δ/1000))).trans_eq
  ring

end ArtinMatthews
