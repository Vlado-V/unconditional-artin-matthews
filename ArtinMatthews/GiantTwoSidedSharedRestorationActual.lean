module

public import ArtinMatthews.GiantTwoSidedSharedRestoration
public import ArtinMatthews.GiantTwoSidedSharedCollisionActual
public import ArtinMatthews.MarkedBonferroniTail


set_option backward.privateInPublic true
@[expose] public section

/-! Restoring the shared-label restrictions costs every fixed log power,
relative to the actual product of the two one-mark damping factors. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators Topology
noncomputable section

theorem giantCandidateSharedNormalizedDamping_log_saving (k : ℕ) (T : ℝ) (hT : 0 ≤ T)
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop,∀ (S : Finset (GiantCandidateGroupIndex x)) (w : ℕ),
      w∈Ioc 0 ⌊T*x⌋₊ →
      let P (i : S) := giantCandidateGroup x i.val
      ∀ (b b' : (i : S) → ↥(P i)), (∀ i,(b i:ℕ) ∣ w) → (∀ i,(b' i:ℕ) ∣ w+1) →
        ‖giantTwoSidedSharedNormalizedDamping k q w b b' -
          giantTwoSidedOneMarkDampingProduct P q w‖ ≤
            (Real.log x)^(-A)*giantTwoSidedOneMarkDampingProduct P q w := by
  obtain ⟨C,hC,hbad⟩ := giantCandidateSharedBadMass_eventually k T hT
  let K := (q⁻¹)^(2*k)
  let c := giantCandidateGroupLogRate*Real.log K
  have hK : 1 ≤ K := one_le_pow₀ ((one_le_inv₀ hq).mpr hq1)
  have hc : 0 ≤ c := mul_nonneg (by unfold giantCandidateGroupLogRate; positivity) (Real.log_nonneg hK)
  have ht := ((rpow_mul_exp_neg_rpow_tendsto (c+2+A)
    (by norm_num : (0:ℝ)<28/100) (by norm_num : (0:ℝ)<1)).comp
      Real.tendsto_log_atTop).const_mul (2*C)
  simp only [Function.comp_def,neg_one_mul,mul_zero] at ht
  filter_upwards [hbad,giantCandidateSelectedGroups_exponential_cost_eventually K hK,
    giantCandidateSelectedGroups_geometry_eventually,giantCandidateFullPrimes_prime_upper_eventually,
    Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ),
    ht.eventually (Iio_mem_nhds (zero_lt_one : (0:ℝ)<1))]
    with x hb hcost hgeo hprime hL hsmall
  intro S w hw
  dsimp only
  intro b b' hbw hb'w
  let P (i : S) := giantCandidateGroup x i.val
  let L := Real.log x
  let R := (q⁻¹)^(2*(k*Fintype.card S))
  let E := Real.exp (-(L^(28/100:ℝ)))
  let B := giantTwoSidedOneMarkDampingProduct P q w
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hB : 0 ≤ B := by unfold B giantTwoSidedOneMarkDampingProduct; positivity
  have hp (i : S) (p : ℕ) (hp : p∈P i) : p.Prime :=
    (hprime p (mem_giantCandidateFullPrimes.mpr ⟨i.val,hp⟩)).1
  have hV (i : S) : 0 < bandReciprocalMass (P i) :=
    (div_pos (Real.log_pos (by norm_num)) (by norm_num)).trans ((hgeo S).2.1 i).1
  have hbad0 : 0 ≤ giantTwoSidedSharedBadMass P k w :=
    markedEventMass_nonneg _ (markedPhysicalPadHarmonicMass_nonneg P k hV) _
  have hR : R ≤ L^c := by
    unfold R
    rw [← Nat.mul_assoc,pow_mul,Fintype.card_coe]
    exact hcost S
  have hR1 : R+1 ≤ 2*L^c := by linarith only [hR,Real.one_le_rpow hL hc]
  have hpows : L^(c+2+A)*L^(-A) = L^c*L^2 := by
    rw [← Real.rpow_add hL0,show c+2+A+(-A)=c+2 by ring,Real.rpow_add hL0,Real.rpow_two]
  have herr : (R+1)*giantTwoSidedSharedBadMass P k w ≤ L^(-A) := by
    calc
      _ ≤ (2*L^c)*(C*L^2*E) := mul_le_mul hR1 (hb S w hw) hbad0 (by positivity)
      _ = (2*C*E)*(L^c*L^2) := by ring
      _ = (2*C*(L^(c+2+A)*E))*L^(-A) := by rw [← hpows]; ring
      _ ≤ 1*L^(-A) := mul_le_mul_of_nonneg_right hsmall.le (Real.rpow_nonneg hL0.le _)
      _ = _ := one_mul _
  exact (giantTwoSidedSharedNormalizedDamping_error hp (hgeo S).1 hV k w b b' hbw hb'w hq hq1).trans
    (mul_le_mul_of_nonneg_right herr hB)

end
end ArtinMatthews
