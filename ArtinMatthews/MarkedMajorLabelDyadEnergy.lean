module

public import ArtinMatthews.MarkedMajorLabelDyadMellin
public import ArtinMatthews.MarkedMajorMellinIsolationL2Actual
public import ArtinMatthews.MarkedMajorArcExceptionalCover


set_option backward.privateInPublic true
@[expose] public section

/-! Actual weighted L² Mellin isolation for a prime-label dyad. This exact
finite analytic adapter retains both band normalization and cofactor mass. -/
namespace ArtinMatthews
open Finset MeasureTheory
open scoped ContDiff

theorem markedMajorLabelDyad_energy_of_isolated
    (η : ℝ → ℂ) (hη : ContDiff ℝ ∞ η) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hsupp : Function.support η ⊆ Set.Icc a b) :
    ∃ C : ℝ,0 < C ∧ ∀ {J : Type} [Fintype J]
      (P : J → Finset ℕ) (_hP : ∀ j p,p ∈ P j → p.Prime)
      (_hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
      (_hV : ∀ j,0 < bandReciprocalMass (P j))
      (S : Finset ℕ) (_hS : ∀ p ∈ S,p.Prime)
      (Y H V θ T : ℝ) (_hY : 0 < Y) (_hH : 0 < H) (_hV₀ : 0 < V)
      (_hlo : ∀ p ∈ S,H ≤ (p:ℝ)) (_hhi : ∀ p ∈ S,(p:ℝ) ≤ 2*H)
      {q : ℕ} (χ : DirichletCharacter ℂ q)
      (M N : ℝ → ℂ) (_hM : Continuous M) (_hN : Continuous N)
      (MB NB E : ℝ) (_hMB : ∀ t,‖M t‖ ≤ MB) (_hNB : ∀ t,‖N t‖ ≤ NB) (_hE : 0 ≤ E),
      (∀ ξ : ℝ,(∫ t in Set.Icc (-T) T,‖markedPrimePolynomial S H χ ξ t*M t*N t‖^2) ≤ E) →
      (∫ t in Set.Icc (-T) T,‖markedMajorLabelDyad P S η χ θ Y V t*M t*N t‖^2) ≤
        C*V⁻¹^2*b^2*(1+|θ|)^4*E := by
  obtain ⟨C,hC,hbound⟩ := markedMellinIsolation_coefficient_uniform_L2_bound η hη ha hsupp
  refine ⟨C,hC,?_⟩
  intro J _ P hP hdis hV S hS Y H V θ T hY hH hV₀ hlo hhi q χ M N hM hN MB NB E hMB hNB hE he
  let R := markedMajorCofactorSet P a b Y H
  let Q := markedMajorCofactorPolynomial P R χ Y H
  let A := fun (ξ t : ℝ) => Complex.exp (-(Complex.I*(ξ:ℂ)*(Real.log Y:ℂ)))*
    markedPrimePolynomial S H χ ξ t*Q (t+ξ)*M t*N t
  have hQ : ∀ t,‖Q t‖ ≤ b := by
    intro t
    apply markedMajorCofactorPolynomial_norm_le P hP hdis hV R (filter_subset _ _) hb hY hH
    intro n hn
    exact (mem_filter.mp hn).2.2
  have hphase : ∀ ξ : ℝ,‖Complex.exp (-(Complex.I*(ξ:ℂ)*(Real.log Y:ℂ)))‖=1 := by
    intro ξ
    rw [Complex.norm_exp]
    simp
  have hnorm (ξ t : ℝ) : ‖A ξ t‖ = ‖Q (t+ξ)‖*‖markedPrimePolynomial S H χ ξ t*M t*N t‖ := by
    dsimp [A]
    simp only [norm_mul,hphase,one_mul]
    ring
  have hAb : ∀ ξ t,‖A ξ t‖ ≤ 2*b*MB*NB := by
    intro ξ t
    rw [hnorm,norm_mul,norm_mul]
    have hp := markedPrimePolynomial_norm_le_two S hH χ ξ t hS hhi
    have hprod := mul_le_mul (mul_le_mul hp (hMB t) (norm_nonneg _) (by norm_num : (0:ℝ)≤2))
      (hNB t) (norm_nonneg _) (mul_nonneg (by norm_num) ((norm_nonneg (M 0)).trans (hMB 0)))
    have h := mul_le_mul (hQ (t+ξ)) hprod
      (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)) hb
    nlinarith
  have hAc : Continuous (fun z : ℝ×ℝ => A z.1 z.2) := by
    dsimp [A,Q]
    unfold markedPrimePolynomial markedMajorCofactorPolynomial markedPrimePhase
    fun_prop
  have hAe : ∀ ξ : ℝ,(∫ t in Set.Icc (-T) T,‖A ξ t‖^2) ≤ b^2*E := by
    intro ξ
    have hc := (markedPrimePolynomial_continuous S H χ ξ).mul hM |>.mul hN
    have hInt : IntegrableOn (fun t => ‖markedPrimePolynomial S H χ ξ t*M t*N t‖^2) (Set.Icc (-T) T) :=
      hc.norm.pow 2 |>.continuousOn.integrableOn_compact isCompact_Icc
    have hAInt : IntegrableOn (fun t => ‖A ξ t‖^2) (Set.Icc (-T) T) := ((hAc.comp (continuous_const.prodMk continuous_id)).norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    calc
      _ ≤ ∫ t in Set.Icc (-T) T,b^2*‖markedPrimePolynomial S H χ ξ t*M t*N t‖^2 := by
        apply integral_mono hAInt (hInt.const_mul (b^2))
        intro t
        change ‖A ξ t‖^2 ≤ b^2*‖markedPrimePolynomial S H χ ξ t*M t*N t‖^2
        rw [hnorm,mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hQ (t+ξ)) 2) (sq_nonneg _)
      _ = b^2*(∫ t in Set.Icc (-T) T,‖markedPrimePolynomial S H χ ξ t*M t*N t‖^2) := integral_const_mul _ _
      _ ≤ b^2*E := mul_le_mul_of_nonneg_left (he ξ) (sq_nonneg _)
  obtain ⟨hInt,hineq⟩ := hbound θ T A (2*b*MB*NB) (b^2*E) hAc hAb (by positivity) hAe
  have hid (t : ℝ) : markedMajorLabelDyad P S η χ θ Y V t*M t*N t =
      (V:ℂ)⁻¹*∫ ξ : ℝ,markedMellinIsolationCoefficient η hη ha hsupp θ ξ*A ξ t := by
    rw [markedMajorLabelDyad_mellin P hP S (fun p hp => (hS p hp).pos) η hη ha hsupp χ θ Y H V t hY hH hlo hhi]
    dsimp [A,Q,R]
    simp only [← mul_assoc,integral_mul_const]
  simp_rw [hid,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hV₀,mul_pow]
  rw [integral_const_mul]
  have h := mul_le_mul_of_nonneg_left hineq (sq_nonneg V⁻¹)
  nlinarith

end ArtinMatthews
