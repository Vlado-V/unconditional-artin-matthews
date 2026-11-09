module

public import ArtinMatthews.MarkedPhysicalEndpointDamping


set_option backward.privateInPublic true
@[expose] public section

/-! Exact arithmetic q-hit factors for the literal physical damping.
The real half-excess exponent becomes the square-root factor at each
inactive prime hit. No differentiation of divisibility is asserted. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedPhysicalExtraPrimes {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (a : MarkedPhysicalMarking P M) (j : J) (u : ℕ) : Finset ℕ :=
  activeDivisors (P j) u \ markedPhysicalLabelSet a j

def markedPhysicalInactivePrimeWeight {J : Type*} [Fintype J]
    (P : J → Finset ℕ) {M : ℕ} (a : MarkedPhysicalMarking P M) (r : ℝ) (u : ℕ) : ℝ :=
  ∏ j,∏ p ∈ P j \ markedPhysicalLabelSet a j,if p ∣ u then r else 1

theorem markedPhysicalInactivePrimeWeight_pow {J : Type*} [Fintype J]
    (P : J → Finset ℕ) {M : ℕ} (a : MarkedPhysicalMarking P M) (r : ℝ) (u : ℕ) :
    markedPhysicalInactivePrimeWeight P a r u = r^(∑ j,(markedPhysicalExtraPrimes a j u).card) := by
  unfold markedPhysicalInactivePrimeWeight
  calc
    _ = ∏ j,r^((markedPhysicalExtraPrimes a j u).card) := by
      apply Finset.prod_congr rfl
      intro j _
      have he : (P j \ markedPhysicalLabelSet a j).filter (fun p => p ∣ u) = markedPhysicalExtraPrimes a j u := by
        ext p
        simp only [Finset.mem_filter,Finset.mem_sdiff,markedPhysicalExtraPrimes,activeDivisors]
        tauto
      rw [Finset.prod_ite,Finset.prod_const,Finset.prod_const_one,mul_one,he]
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

theorem markedPhysical_extra_card {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (a : MarkedPhysicalMarking P M) (ha : MarkedPhysicalMarkingDistinct a) {u : ℕ}
    (hd : ∀ j k,(a j k:ℕ) ∣ u) (j : J) :
    bandCount (P j) u = (markedPhysicalExtraPrimes a j u).card+M := by
  have hsub : markedPhysicalLabelSet a j ⊆ activeDivisors (P j) u := by
    intro p hp
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_filter.mpr ⟨(a j k).2,hd j k⟩
  have hc := Finset.card_sdiff_add_card_eq_card hsub
  rw [markedPhysicalLabelSet_card a ha j] at hc
  exact hc.symm

theorem markedPhysical_excess_eq_extra {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M : ℕ} (a : MarkedPhysicalMarking P M)
    (ha : MarkedPhysicalMarkingDistinct a) {u : ℕ} (hd : ∀ j k,(a j k:ℕ) ∣ u) :
    ((∑ j,bandCount (P j) u:ℕ):ℝ)-(Fintype.card J:ℝ)*M =
      ((∑ j,(markedPhysicalExtraPrimes a j u).card:ℕ):ℝ) := by
  have hc : ∑ j,bandCount (P j) u = (∑ j,(markedPhysicalExtraPrimes a j u).card)+Fintype.card J*M := by
    simp_rw [markedPhysical_extra_card a ha hd]
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id]
  have hr := congrArg (fun n : ℕ => (n:ℝ)) hc
  push_cast at hr
  push_cast
  linarith

theorem markedPhysicalEndpointDamping_eq_inactive {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (M : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (Z : Finset (ℤ × ℤ)) (s : MarkedPhysicalState P M Z) :
    markedPhysicalEndpointDamping P M q s.1.1.1 =
      markedPhysicalInactivePrimeWeight P s.1.2 (Real.sqrt q) s.1.1.1.1.natAbs := by
  have hd (j : J) (k : Fin M) : (s.1.2 j k:ℕ) ∣ s.1.1.1.1.natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr (s.2.2.2 j k)
  unfold markedPhysicalEndpointDamping
  rw [markedPhysical_excess_eq_extra s.1.2 s.2.2.1 hd,
    Real.rpow_div_two_eq_sqrt _ hq,Real.rpow_natCast,markedPhysicalInactivePrimeWeight_pow]

theorem markedPhysicalInactivePrimeWeight_nonneg {J : Type*} [Fintype J]
    (P : J → Finset ℕ) {M : ℕ} (a : MarkedPhysicalMarking P M) {r : ℝ} (hr : 0 ≤ r) (u : ℕ) :
    0 ≤ markedPhysicalInactivePrimeWeight P a r u := by
  rw [markedPhysicalInactivePrimeWeight_pow]
  exact pow_nonneg hr _

theorem markedPhysicalInactivePrimeWeight_le_one {J : Type*} [Fintype J]
    (P : J → Finset ℕ) {M : ℕ} (a : MarkedPhysicalMarking P M) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (u : ℕ) : markedPhysicalInactivePrimeWeight P a r u ≤ 1 := by
  rw [markedPhysicalInactivePrimeWeight_pow]
  exact pow_le_one₀ hr hr1

theorem markedPhysicalInactivePrimeWeight_complement {J : Type*} [Fintype J]
    (P : J → Finset ℕ) {M : ℕ} (a : MarkedPhysicalMarking P M) (r : ℝ) (u : ℕ) :
    markedPhysicalInactivePrimeWeight P a r u =
      ∏ j,(∏ p ∈ P j \ markedPhysicalLabelSet a j,(1-(1-r)*(if p ∣ u then (1:ℝ) else 0))) := by
  unfold markedPhysicalInactivePrimeWeight
  apply Finset.prod_congr rfl
  intro j _
  apply Finset.prod_congr rfl
  intro p _
  split_ifs <;> ring

end ArtinMatthews
