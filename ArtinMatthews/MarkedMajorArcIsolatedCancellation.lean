module

public import ArtinMatthews.MarkedMajorArcIsolatedEnergy
public import ArtinMatthews.MarkedMajorArcNormalizedProductMean
public import ArtinMatthews.MarkedMajorArcProductBudget


set_option backward.privateInPublic true
@[expose] public section

/-! Arbitrary logarithmic saving for the actual isolated-prime major-arc
energy. Every arithmetic and analytic input is instantiated with its proved
source; only the explicit scale and coefficient support conditions remain. -/
namespace ArtinMatthews
open Finset Filter MeasureTheory
open scoped Topology

 theorem marked_major_isolated_prime_cancellation
    (c C₁ C₂ d a η τ C b K σ b₀ D P : ℝ)
    (hc : 0 < c) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hd : 0 < d)
    (ha : 0 ≤ a) (hη : 0 < η) (hτ : 0 < τ) (hC : 0 ≤ C)
    (hσ : 0 ≤ σ) (hb₀ : 0 ≤ b₀) (hD : 0 ≤ D) (hP : 0 ≤ P) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (Y T H u v U : ℝ) (l r : ℕ) (β : ℕ → ℂ),
        1 < Y → c*L^(1/(10:ℝ)) ≤ Real.log Y →
        Real.log Y ≤ C₁*L^(1/(5:ℝ)) → 1 < T → Real.log T ≤ C₂*L →
        T ≤ K*Real.exp L*L^b → Real.exp (τ*L) ≤ H → H ≤ u → u ≤ v →
        v ≤ 2*H → v ≤ Real.exp (η*L) → Real.exp (d*L) ≤ U →
        U ≤ (l:ℝ) → (r:ℝ) ≤ 2*U → H*U ≤ Real.exp (σ*L) → T/(H*U) ≤ L^b₀ →
        (∀ n ∈ Icc l r, ‖β n‖ ≤ L^D) →
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (modulation : ℝ),
          (q:ℝ) ≤ L^a → |modulation| ≤ L^C →
          ∀ (k : ℕ) (χp : DirichletCharacter ℂ k) (ξ : ℝ) (S : Finset ℕ),
            (∀ p ∈ S, p.Prime) → (∀ p ∈ S, (p:ℝ) ≤ 2*Y) →
            (∫ t in Set.Icc (-T) T,
              ‖markedPrimePolynomial S Y χp ξ t*
                markedMajorCenteredSum χ (Real.exp (L^(6/25:ℝ))) modulation t H u v*
                markedDyadicPolynomial l r U β t‖^2) ≤ L^(-P) := by
  let A := b₀+2*D+P+7
  let R := P+D+2
  have hA : 0 ≤ A := by dsimp [A]; linarith
  have hR : 0 ≤ R := by dsimp [R]; linarith
  obtain ⟨J,hJ,hisolated⟩ := marked_isolated_prime_energy_of_mean c C₁ C₂ A d hc hC₁ hC₂ hA hd
  obtain ⟨E,hE,hbudget⟩ := marked_product_mean_envelope_uniform σ b₀ D hσ hb₀
  filter_upwards [hisolated,hbudget,
    marked_major_long_coefficient a η τ C b K R ha hη hτ hC hR,
    eventually_ge_atTop (max 1 (max (1/τ) (E+4*J)))] with L hi hb hlong hL
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hEL : E+4*J ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hτL : 1 ≤ τ*L := by
    have hh := (div_le_iff₀ hτ).mp ((le_max_left _ _).trans ((le_max_right _ _).trans hL))
    nlinarith
  intro Y T H u v U l r β hY hYlo hYhi hT hTlog hTupper hH hHu huv hvH hvhi hU hl hr hHU hratio hβ
    q _ χ modulation hq hmod k χp ξ S hS hScap
  let W := Real.exp (L^(6/25:ℝ))
  let M := fun t => markedMajorCenteredSum χ W modulation t H u v
  have hHp : 0 < H := (Real.exp_pos _).trans_le hH
  have hUp : 0 < U := (Real.exp_pos _).trans_le hU
  have hH1 : 1 ≤ H := (Real.one_le_exp (by positivity : 0 ≤ τ*L)).trans hH
  have hU1 : 1 ≤ U := (Real.one_le_exp (by positivity : 0 ≤ d*L)).trans hU
  have hX : 1 ≤ H*U := by nlinarith
  have hlog : 1 ≤ Real.log u := hτL.trans ((Real.le_log_iff_exp_le (hHp.trans_le hHu)).mpr (hH.trans hHu))
  have hMb : ∀ t ∈ Set.Icc (-T) T, ‖M t‖ ≤ L^(-R) := by
    intro t ht
    exact hlong q χ modulation t H u v hq hmod ((abs_le.mpr ht).trans hTupper) hH hHu huv hvH hvhi
  have hmean : (∫ t in Set.Icc (-T) T, ‖M t*markedDyadicPolynomial l r U β t‖^2) ≤ E*L^(b₀+2*D+5) := by
    have hm := marked_centered_dyadic_product_mean χ W modulation H u v U T 0 (L^D) l r β
      hHp hUp (by linarith) (Real.rpow_nonneg hLp.le _) hHu hvH hlog hl hr hβ
    simp only [add_zero] at hm
    rw [intervalIntegral.integral_of_le (by linarith),← integral_Icc_eq_integral_Ioc] at hm
    exact hm.trans (hb H U T hHp hUp hX (by linarith) hHU hratio)
  have hh := hi Y T U (L^D) (L^(-R)) (E*L^(b₀+2*D+5)) l r β M
    hY hYlo hYhi hT hTlog hU hl hr hβ (marked_centered_sum_continuous χ W modulation H u v)
    hMb hmean k χp ξ S hS hScap
  have hsquare (z : ℝ) : (L^z)^2 = L^(z*2) := by
    rw [Real.rpow_mul hLp.le,Real.rpow_two]
  have hgood : (L^(-A))^2*(E*L^(b₀+2*D+5)) ≤ E*L^(-P-1) := by
    rw [hsquare]
    have he : L^(-A*2)*(E*L^(b₀+2*D+5)) = E*L^(-A*2+(b₀+2*D+5)) := by
      rw [Real.rpow_add hLp (-A*2) (b₀+2*D+5)]; ring
    rw [he]
    apply mul_le_mul_of_nonneg_left _ hE.le
    apply Real.rpow_le_rpow_of_exponent_le hL1
    dsimp [A]
    linarith
  have hbad : 4*(L^(-R))^2*J*L*(L^D)^2 ≤ 4*J*L^(-P-1) := by
    have he : 4*(L^(-R))^2*J*L*(L^D)^2 = 4*J*L^(-R*2+1+D*2) := by
      rw [Real.rpow_add hLp (-R*2+1) (D*2),Real.rpow_add hLp (-R*2) 1,Real.rpow_one,
        hsquare,hsquare]
      ring
    rw [he]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le hL1
    dsimp [R]
    linarith
  apply hh.trans
  calc
    _ ≤ E*L^(-P-1)+4*J*L^(-P-1) := add_le_add hgood hbad
    _ = (E+4*J)*L^(-P-1) := by ring
    _ ≤ L*L^(-P-1) := mul_le_mul_of_nonneg_right hEL (Real.rpow_nonneg hLp.le _)
    _ = L^(-P) := by
      conv_lhs => lhs; rw [← Real.rpow_one L]
      rw [← Real.rpow_add hLp]
      congr 1
      ring

end ArtinMatthews
