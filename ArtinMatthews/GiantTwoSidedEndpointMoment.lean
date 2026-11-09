module

public import ArtinMatthews.GiantTwoSidedEndpointQuotient
public import ArtinMatthews.GiantCandidateSquareCore
public import ArtinMatthews.GiantOrderedProductMoment


set_option backward.privateInPublic true
@[expose] public section

/-! For each actual ordered list, the endpoint norm is bounded by the
moment on its exact quotient interval. The divisor moment follows from
the real ordered factorization fibers. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantTwoSidedEndpoint_damped_norm_le {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (M : ℕ) {q : ℝ} (hq : q ∈ Set.Icc (0:ℝ) 1)
    (F : ℕ → ℂ) (n : ℕ) :
    ‖(giantTwoSidedEndpointDamping P M q n:ℂ)*F n‖ ≤ ‖F n‖ := by
  have h := giantTwoSidedEndpointDamping_mem_unitInterval P M hq n
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg h.1]
  exact mul_le_of_le_one_left (norm_nonneg _) h.2

theorem giantTwoSidedEndpointPositions_energy_le_quotient_sum {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    {M N : ℕ} {Z : Finset ℕ} (hZ : Z ⊆ Ioc 0 N) {q : ℝ} (hq : q ∈ Set.Icc (0:ℝ) 1)
    (a : MarkedPhysicalMarking P M) (F : ℕ → ℂ) (B : ℕ → ℝ)
    (hF : ∀ n : GiantTwoSidedEndpointPositions Z a, ‖F n.1.val‖ ≤ B (giantTwoSidedEndpointQuotient a n)) :
    (∑ n : GiantTwoSidedEndpointPositions Z a,
      ‖(giantTwoSidedEndpointDamping P M q n.1.val:ℂ)*F n.1.val‖^2) ≤
        ∑ m ∈ Ioc 0 (N/markedPhysicalMarkingProduct a),(B m)^2 := by
  classical
  apply sum_le_sum_of_injOn (giantTwoSidedEndpointQuotient a)
    (giantTwoSidedEndpointQuotient_injective hP hdis a).injOn
  · intro m hm
    obtain ⟨n,_,rfl⟩ := mem_image.mp hm
    exact giantTwoSidedEndpointQuotient_mem hP hdis hZ a n
  · intro n _
    exact pow_le_pow_left₀ (norm_nonneg _)
      ((giantTwoSidedEndpoint_damped_norm_le P M hq F n.1.val).trans (hF n)) 2
  · intro _ _ _
    exact sq_nonneg _

theorem giantTwoSidedEndpointPositions_energy_le_uniform {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    {M N : ℕ} {Z : Finset ℕ} (hZ : Z ⊆ Ioc 0 N) {q : ℝ} (hq : q ∈ Set.Icc (0:ℝ) 1)
    (a : MarkedPhysicalMarking P M) (F : ℕ → ℂ) {C : ℝ}
    (hF : ∀ n ∈ Z, ‖F n‖ ≤ C) :
    (∑ n : GiantTwoSidedEndpointPositions Z a,
      ‖(giantTwoSidedEndpointDamping P M q n.1.val:ℂ)*F n.1.val‖^2) ≤
        C^2*(N:ℝ)*markedPhysicalReciprocalProduct a := by
  let D := markedPhysicalMarkingProduct a
  have hdiv : ((N/D:ℕ):ℝ) ≤ (N:ℝ)/(D:ℝ) := Nat.cast_div_le
  calc
    _ ≤ ∑ _m ∈ Ioc 0 (N/D),C^2 :=
      giantTwoSidedEndpointPositions_energy_le_quotient_sum hP hdis hZ hq a F (fun _ => C)
        (fun n => hF n.1.val n.1.property)
    _ = C^2*((N/D:ℕ):ℝ) := by simp only [sum_const,Nat.card_Ioc,Nat.sub_zero,nsmul_eq_mul,mul_comm]
    _ ≤ C^2*((N:ℝ)/(D:ℝ)) := mul_le_mul_of_nonneg_left hdiv (sq_nonneg _)
    _ = _ := by rw [markedPhysicalReciprocalProduct_eq]; unfold D; ring

theorem giantTwoSidedEndpointPositions_energy_le_fiber {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    {M N : ℕ} {Z : Finset ℕ} (hZ : Z ⊆ Ioc 0 N) {q : ℝ} (hq : q ∈ Set.Icc (0:ℝ) 1)
    (a : MarkedPhysicalMarking P M) (F : ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (r : ℕ) (hr : 0 < r)
    (hF : ∀ n ∈ Z, ‖F n‖ ≤ C*((giantOrderedProductFiber r (giantCandidateStrip (univ.biUnion P) n)).card:ℝ)) :
    (∑ n : GiantTwoSidedEndpointPositions Z a,
      ‖(giantTwoSidedEndpointDamping P M q n.1.val:ℂ)*F n.1.val‖^2) ≤
        C^2*(N:ℝ)*(1+Real.log ((N:ℝ)+1))^(r*r)*markedPhysicalReciprocalProduct a := by
  let D := markedPhysicalMarkingProduct a
  let Q := N/D
  let B (m : ℕ) : ℝ := C*((giantOrderedProductFiber r m).card:ℝ)
  have hquot (n : GiantTwoSidedEndpointPositions Z a) : ‖F n.1.val‖ ≤ B (giantTwoSidedEndpointQuotient a n) := by
    have hn := (mem_Ioc.mp (hZ n.1.property)).1
    have hq0 := (mem_Ioc.mp (giantTwoSidedEndpointQuotient_mem hP hdis hZ a n)).1
    have hd := giantCandidateStrip_dvd_markedQuotient hP hdis a n.2.1 hn n.2.2
    have hc := giantOrderedProductFiber_card_le_of_dvd r hr hq0 hd
    exact (hF n.1.val n.1.property).trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hc) hC)
  have hdiv : (Q:ℝ) ≤ (N:ℝ)/(D:ℝ) := Nat.cast_div_le
  have hlog : Real.log (Q:ℝ) ≤ Real.log ((N:ℝ)+1) := by
    have hN1 : 1 ≤ (N:ℝ)+1 := le_add_of_nonneg_left (Nat.cast_nonneg N)
    by_cases h : Q=0
    · simp only [h,Nat.cast_zero,Real.log_zero]
      exact Real.log_nonneg hN1
    · have hle : (Q:ℝ) ≤ N := Nat.cast_le.mpr (Nat.div_le_self N D)
      exact Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h)) (by linarith)
  have hpow : (1+Real.log (Q:ℝ))^(r*r) ≤ (1+Real.log ((N:ℝ)+1))^(r*r) :=
    pow_le_pow_left₀ (add_nonneg zero_le_one (Real.log_natCast_nonneg Q))
      (add_le_add (le_refl (1:ℝ)) hlog) _
  calc
    _ ≤ ∑ m ∈ Ioc 0 Q,(B m)^2 :=
      giantTwoSidedEndpointPositions_energy_le_quotient_sum hP hdis hZ hq a F B hquot
    _ = C^2*∑ m ∈ Ioc 0 Q,((giantOrderedProductFiber r m).card:ℝ)^2 := by
      simp only [B,mul_pow,Finset.mul_sum]
    _ ≤ C^2*((Q:ℝ)*(1+Real.log (Q:ℝ))^(r*r)) :=
      mul_le_mul_of_nonneg_left (giant_ordered_product_fiber_second_moment r Q) (sq_nonneg _)
    _ ≤ C^2*(((N:ℝ)/(D:ℝ))*(1+Real.log ((N:ℝ)+1))^(r*r)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hdiv hpow (by positivity) (by positivity)) (sq_nonneg _)
    _ = _ := by rw [markedPhysicalReciprocalProduct_eq]; unfold D; ring

end
end ArtinMatthews
