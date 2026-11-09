module

public import ArtinMatthews.MarkedMajorLabelMeanBudget
public import ArtinMatthews.MarkedMajorLabelPolynomial
public import ArtinMatthews.MarkedMajorArcNormalizedProductMean
public import ArtinMatthews.MarkedSparsePhaseContinuity


set_option backward.privateInPublic true
@[expose] public section

/-! The literal normalized endpoint Q = B M N and its coarse mean-square
bound, uniform over every real translate and every positive interval length. -/
namespace ArtinMatthews
open Finset Filter MeasureTheory
open scoped Topology

noncomputable def markedMajorLabelEndpoint {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) {k q : ℕ}
    (χb : DirichletCharacter ℂ k) (θ Y : ℝ) (χ : DirichletCharacter ℂ q)
    (W modulation H u v U : ℝ) (l r : ℕ) (β : ℕ → ℂ) (t : ℝ) : ℂ :=
  markedMajorLabelPolynomial bands cutoff χb θ Y t*
    markedMajorCenteredSum χ W modulation t H u v*markedDyadicPolynomial l r U β t

theorem markedMajorLabelEndpoint_continuous {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) {k q : ℕ}
    (χb : DirichletCharacter ℂ k) (θ Y : ℝ) (χ : DirichletCharacter ℂ q)
    (W modulation H u v U : ℝ) (l r : ℕ) (β : ℕ → ℂ) :
    Continuous (markedMajorLabelEndpoint bands cutoff χb θ Y χ W modulation H u v U l r β) := by
  apply Continuous.mul
  · apply Continuous.mul
    · unfold markedMajorLabelPolynomial markedPrimePhase
      fun_prop
    · exact marked_centered_sum_continuous χ W modulation H u v
  · exact markedDyadicPolynomial_continuous l r U β

theorem marked_major_label_translated_mean (σ D B : ℝ) (hσ : 0 ≤ σ) (hB : 0 ≤ B)
    (cutoff : ℝ → ℂ) (hcutoff : ∀ y,‖cutoff y‖ ≤ 1)
    (hsupp : Function.support cutoff ⊆ Set.Iic B) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ L : ℝ in atTop,∀ {J : Type} [Fintype J]
      (bands : J → Finset ℕ),
      (∀ j p,p ∈ bands j → p.Prime) →
      Pairwise (fun i j => Disjoint (bands i) (bands j)) →
      (∀ j,0 < bandReciprocalMass (bands j)) →
      ∀ (Y θ H u v U T ξ : ℝ) (l r : ℕ) (β : ℕ → ℂ),
      0 < Y → 0 < H → 0 < U → 0 < T → 1 ≤ H*U → H*U ≤ Real.exp (σ*L) →
      H ≤ u → v ≤ 2*H → 1 ≤ Real.log u → U ≤ (l:ℝ) → (r:ℝ) ≤ 2*U →
      (∀ n ∈ Icc l r,‖β n‖ ≤ L^D) →
      ∀ (k q : ℕ) (χb : DirichletCharacter ℂ k) (χ : DirichletCharacter ℂ q) (modulation : ℝ),
      (∫ t in Set.Icc (-T) T,
        ‖markedMajorLabelEndpoint bands cutoff χb θ Y χ (Real.exp (L^(6/25:ℝ))) modulation H u v U l r β (t+ξ)‖^2) ≤
          C*L^(2*D+5)*(1+T/(H*U)) := by
  obtain ⟨C,hC,hbudget⟩ := marked_product_mean_envelope_uniform_all_lengths σ D hσ
  refine ⟨B^2*C+1,by positivity,?_⟩
  filter_upwards [hbudget,eventually_ge_atTop (1:ℝ)] with L hb hL
  have hLp : 0 < L := zero_lt_one.trans_le hL
  intro J _ bands hbands hdis hV Y θ H u v U T ξ l r β hY hH hU hT hX hXupper hHu hv hlog hl hr hβ
    k q χb χ modulation
  let W := Real.exp (L^(6/25:ℝ))
  let MN := fun t => markedMajorCenteredSum χ W modulation (t+ξ) H u v*
    markedDyadicPolynomial l r U β (t+ξ)
  have hMN : Continuous MN := by
    apply Continuous.mul
    · exact (marked_centered_sum_continuous χ W modulation H u v).comp (continuous_id.add continuous_const)
    · exact (markedDyadicPolynomial_continuous l r U β).comp (continuous_id.add continuous_const)
  have hMNi : IntegrableOn (fun t => ‖MN t‖^2) (Set.Icc (-T) T) :=
    (hMN.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hQi : IntegrableOn
      (fun t => ‖markedMajorLabelEndpoint bands cutoff χb θ Y χ W modulation H u v U l r β (t+ξ)‖^2)
      (Set.Icc (-T) T) := by
    exact (((markedMajorLabelEndpoint_continuous bands cutoff χb θ Y χ W modulation H u v U l r β).comp
      (continuous_id.add continuous_const)).norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hmean := marked_centered_dyadic_product_mean χ W modulation H u v U T ξ (L^D) l r β
    hH hU hT (by positivity) hHu hv hlog hl hr hβ
  rw [intervalIntegral.integral_of_le (by linarith),← integral_Icc_eq_integral_Ioc] at hmean
  have hcoarse := hmean.trans (hb H U T hH hU hX hT.le hXupper)
  calc
    _ ≤ ∫ t in Set.Icc (-T) T,B^2*‖MN t‖^2 := by
      apply integral_mono hQi (hMNi.const_mul (B^2))
      intro t
      change ‖markedMajorLabelEndpoint bands cutoff χb θ Y χ W modulation H u v U l r β (t+ξ)‖^2 ≤ _
      have hnorm := markedMajorLabelPolynomial_norm_le bands hbands hdis hV cutoff hB hcutoff hsupp χb θ Y (t+ξ) hY
      unfold markedMajorLabelEndpoint
      rw [mul_assoc,norm_mul,mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) (sq_nonneg _)
    _ = B^2*(∫ t in Set.Icc (-T) T,‖MN t‖^2) := integral_const_mul _ _
    _ ≤ B^2*(C*L^(2*D+5)*(1+T/(H*U))) := mul_le_mul_of_nonneg_left hcoarse (sq_nonneg _)
    _ ≤ _ := by
      have hp : 0 ≤ L^(2*D+5)*(1+T/(H*U)) := by positivity
      nlinarith only [hp]

end ArtinMatthews
