module

public import ArtinMatthews.MarkedRawBadRootArcMajorant
public import ArtinMatthews.MarkedRootArcIntegrals


set_option backward.privateInPublic true
@[expose] public section

/-! The positive elementary-arc cover remains small on average. This is
the main term needed by finite-interval weighted root counting. -/
namespace ArtinMatthews
noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

theorem markedRawFirstRootArc_integrable {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M : ℕ} (a : MarkedRawActive P M) (d₀ Y : ℝ) :
    Integrable (markedRawFirstRootArcMajorant a d₀ Y) volume :=
  markedFiniteIndicatorSum_integrable _ (fun _ => measurableSet_markedBadRootMultiple _ _)

theorem markedRawFirstRootArc_integral_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M : ℕ} (a : MarkedRawActive P M) (d₀ : ℝ)
    {Y : ℝ} (hY : 0 < Y) :
    (∫ θ : AddCircle (1:ℝ),markedRawFirstRootArcMajorant a d₀ Y θ) ≤
      2*(M:ℝ)^(Fintype.card J)*Y^(-1/2:ℝ) := by
  unfold markedRawFirstRootArcMajorant markedFirstRootArcSet
  rw [markedFiniteIndicatorSum_integral _ (fun _ => measurableSet_markedBadRootMultiple _ _)]
  have hcard : (Fintype.card (markedRawDyadicOmissions a d₀):ℝ) ≤ (M:ℝ)^(Fintype.card J) := by
    have hn := Fintype.card_le_of_injective
      (fun c : markedRawDyadicOmissions a d₀ => c.1) Subtype.val_injective
    simp only [Fintype.card_fun,Fintype.card_fin] at hn
    exact_mod_cast hn
  calc
    _ ≤ ∑ _p : (markedRawDyadicOmissions a d₀) × ↥(Finset.Icc 1 ⌊Y^(1/5:ℝ)⌋₊),2*Y^(-7/10:ℝ) := by
      apply Finset.sum_le_sum
      intro p _
      apply markedBadRootMultiple_real_measure_le
      · have hp : 0 < markedSourceCopiedProduct (markedRawNumericActive a) p.1.1 :=
          Finset.prod_pos (fun j _ => Finset.prod_pos (fun k _ => (a j k).1.2.pos))
        exact_mod_cast (Nat.mul_pos hp (Finset.mem_Icc.mp p.2.2).1).ne'
      · exact Real.rpow_nonneg hY.le _
    _ = 2*(Fintype.card (markedRawDyadicOmissions a d₀):ℝ)*(⌊Y^(1/5:ℝ)⌋₊:ℝ)*Y^(-7/10:ℝ) := by
      simp [Fintype.card_prod]; ring
    _ ≤ 2*(M:ℝ)^(Fintype.card J)*Y^(1/5:ℝ)*Y^(-7/10:ℝ) := by
      gcongr
      exact Nat.floor_le (Real.rpow_nonneg hY.le _)
    _ = _ := by rw [mul_assoc,mul_assoc,← Real.rpow_add hY]; norm_num; ring

theorem markedRawBetaRootArc_integrable {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ)
    (a : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x)) :
    Integrable (markedRawBetaRootArcMajorant e x a) volume := by
  apply integrable_finsetSum
  intro p _
  by_cases hp : p.2 ∈ p.1 ∧ (∀ j ∈ p.1,e j ≤ e p.2)
  · simp only [ite_eq_left hp]
    exact (markedWeightedPairRootArc_integrable _ _ _ _).div_const _
  · simp only [ite_eq_right hp]
    exact integrable_const 0

theorem markedRawBetaRootArc_integral_eventually {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (hinj : Function.Injective e) :
    ∀ᶠ x : ℝ in atTop,∀ a : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x),
      (∫ θ : AddCircle (1:ℝ),markedRawBetaRootArcMajorant e x a θ) ≤
        (200*(2:ℝ)^(Fintype.card J)*(Fintype.card J:ℝ))*
          Real.exp (-(1/2:ℝ)*(Real.log x)^(1/10:ℝ)) := by
  let GoodPair := {p : Finset J × J // p.2 ∈ p.1 ∧ (∀ j ∈ p.1,e j ≤ e p.2)}
  have hcard := eventually_all.mpr (fun p : GoodPair =>
    markedRawDirtyFullTrials_card_eventually e he hinj p.1.1 p.1.2 p.2.2 (by norm_num : (0:ℝ)<1/8))
  have hprob := eventually_all.mpr (fun I : Finset J =>
    marked_actual_harmonic_fresh_probability_eventually (fun j : ↥(Finset.univ \ I) => e j.1)
      (fun j => by linarith [he j.1]))
  filter_upwards [hcard,hprob,Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
    with x hc hμ hlog
  intro a
  have hi (p : Finset J × J) : Integrable (fun θ : AddCircle (1:ℝ) =>
      if p.2 ∈ p.1 ∧ (∀ j ∈ p.1,e j ≤ e p.2) then
        (∑ t : MarkedFreshPrimeTuple (fun j : ↥(Finset.univ \ p.1) => e j.1) x,
          markedFreshHarmonicLaw (fun j : ↥(Finset.univ \ p.1) => e j.1) x t *
          markedPairRootArcMajorant (markedRawDirtyFullTrials e x a (p.1.erase p.2))
            (markedFreshIntegerProduct (fun j : ↥(Finset.univ \ p.1) => e j.1) x t)
            (100*Real.exp (-((Real.log x)^(e p.2)))) θ)/Real.exp (-((Real.log x)^(e p.2))/4)
      else 0) volume := by
    by_cases hp : p.2 ∈ p.1 ∧ (∀ j ∈ p.1,e j ≤ e p.2)
    · simp only [ite_eq_left hp]
      exact (markedWeightedPairRootArc_integrable _ _ _ _).div_const _
    · simp only [ite_eq_right hp]
      exact integrable_const 0
  unfold markedRawBetaRootArcMajorant
  rw [integral_finsetSum _ (fun p _ => hi p)]
  calc
    _ ≤ ∑ _p : Finset J × J,200*Real.exp (-(1/2:ℝ)*(Real.log x)^(1/10:ℝ)) := by
      apply Finset.sum_le_sum
      intro p _
      by_cases hp : p.2 ∈ p.1 ∧ (∀ j ∈ p.1,e j ≤ e p.2)
      · simp only [ite_eq_left hp]
        have h := markedThresholdRootArc_integral_le (markedRawDirtyFullTrials e x a (p.1.erase p.2))
          (markedFreshIntegerProduct (fun j : ↥(Finset.univ \ p.1) => e j.1) x)
          (markedFreshIntegerProduct_ne_zero _ x) _ (hμ p.1).1 (hμ p.1).2 ((Real.log x)^(e p.2))
        apply h.trans
        calc
          _ ≤ 200*(Real.exp ((1/8:ℝ)*(Real.log x)^(e p.2)))^2*
              Real.exp (-3*(Real.log x)^(e p.2)/4) := by gcongr; exact hc (⟨p,hp⟩ : GoodPair) a
          _ = 200*Real.exp (-(1/2:ℝ)*(Real.log x)^(e p.2)) := by
            rw [← Real.exp_nat_mul,mul_assoc,← Real.exp_add]
            congr 2
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
            (by linarith [Real.rpow_le_rpow_of_exponent_le hlog (he p.2)])) (by norm_num)
      · simp only [ite_eq_right hp,integral_const,smul_zero]
        positivity
    _ = _ := by simp [Fintype.card_prod,Fintype.card_finset]; ring

theorem markedRawBadRootArc_integral_log_saving {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (hinj : Function.Injective e) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop,∀ d₀ Y : ℝ,Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y →
      ∀ a : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x),
        (∫ θ : AddCircle (1:ℝ),markedRawBadRootArcMajorant e x d₀ Y a θ) ≤ (Real.log x)^(-A) := by
  let K := Fintype.card J
  have hfirst := marked_polynomial_exp_eventually_le ((2:ℝ)^(K+1)) ((K:ℝ)/100) A
    (by norm_num : (0:ℝ)<1/10) (by norm_num : (0:ℝ)<1/2) (by norm_num : (0:ℝ)<1/2)
  have hsecond := marked_polynomial_exp_eventually_le (200*(2:ℝ)^K*(K:ℝ)) 0 A
    (by norm_num : (0:ℝ)<1/10) (by norm_num : (0:ℝ)<1/2) (by norm_num : (0:ℝ)<1/2)
  filter_upwards [markedRawBetaRootArc_integral_eventually e he hinj,
    Real.tendsto_log_atTop.eventually hfirst,Real.tendsto_log_atTop.eventually hsecond,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hb hf hs hlog
  intro d₀ Y hY a
  have hYpos : 0 < Y := (Real.exp_pos _).trans_le hY
  have hpow : Y^(-1/2:ℝ) ≤ Real.exp (-(1/2:ℝ)*(Real.log x)^(1/10:ℝ)) := by
    convert marked_length_negative_rpow_le (c := 1) (τ := (1/2:ℝ)) (by norm_num)
      (by simpa only [one_mul] using hY) using 1 <;> norm_num
  have hp := markedPadSlots_pow_le K hlog
  have hfm : (∫ θ : AddCircle (1:ℝ),markedRawFirstRootArcMajorant a d₀ Y θ) ≤
      (1/2:ℝ)*(Real.log x)^(-A) := by
    apply (markedRawFirstRootArc_integral_le a d₀ hYpos).trans
    calc
      _ ≤ 2*((2:ℝ)^K*(Real.log x)^((K:ℝ)/100))*
          Real.exp (-(1/2:ℝ)*(Real.log x)^(1/10:ℝ)) := by gcongr
      _ = (2:ℝ)^(K+1)*(Real.log x)^((K:ℝ)/100)*
          Real.exp (-(1/2:ℝ)*(Real.log x)^(1/10:ℝ)) := by rw [pow_succ]; ring
      _ ≤ _ := hf
  have hsm := (hb a).trans (by simpa only [Real.rpow_zero,mul_one] using hs)
  unfold markedRawBadRootArcMajorant
  rw [integral_add (markedRawFirstRootArc_integrable a d₀ Y)
    (markedRawBetaRootArc_integrable e x a)]
  exact (add_le_add hfm hsm).trans_eq (by ring)

end
end ArtinMatthews
