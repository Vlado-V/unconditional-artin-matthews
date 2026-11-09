module

public import ArtinMatthews.MarkedTypeIILabelDyads
public import ArtinMatthews.GiantMarkedBilinearFinite


set_option backward.privateInPublic true
@[expose] public section

/-! The literal selected-label dyadic term after moving damping to the
actual common quotient. The endpoint support and quotient are exact. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

def markedTypeIIQuotientDampedCore {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (F : ℕ → ℂ) (h : ℕ) : ℂ :=
  F h*(1/2:ℂ)^(∑ j,bandCount (P j) h)

theorem markedTypeIIQuotientDampedCore_norm_le {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (F : ℕ → ℂ) (h : ℕ) (hF : ‖F h‖≤1) :
    ‖markedTypeIIQuotientDampedCore P F h‖≤1 := by
  have hhalf : ‖(1/2:ℂ)‖=(1/2:ℝ) := by norm_num [norm_div]
  unfold markedTypeIIQuotientDampedCore
  rw [norm_mul,norm_pow,hhalf]
  exact (mul_le_mul hF (pow_le_one₀ (by norm_num) (by norm_num))
    (by positivity) (by norm_num : (0:ℝ)≤1)).trans_eq (one_mul _)

def markedTypeIILabelEndpointCoefficient {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (Y : ℝ) (α β : ℕ → ℂ) (a : MarkedTypeIIEndpoint) : ℂ :=
  (markedMajorLabelMass P:ℂ)*markedTypeIILabelCutoff ((a.label:ℝ)/Y)*α a.leftFactor*β a.rightFactor

def markedTypeIIOccupiedLabelEndpoints {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (Y : ℝ) (M N : Finset ℕ) : Finset MarkedTypeIIEndpoint :=
  (giantMarkedEndpoints P M N).filter (fun a => markedTypeIILabelCutoff ((a.label:ℝ)/Y)≠0)

def markedTypeIISelectedLabelDyadSum {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (Y : ℝ) (M N : Finset ℕ) (α β F : ℕ → ℂ) : ℂ :=
  ∑ a∈giantMarkedEndpoints P M N,if a.label∣a.value-1 then
    markedTypeIIQuotientDampedCore P F ((a.value-1)/a.label)*
      markedTypeIILabelEndpointCoefficient P Y α β a else 0

theorem markedTypeIISelectedLabelDyadSum_eq_filtered {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (Y : ℝ) (M N : Finset ℕ) (α β F : ℕ → ℂ) :
    markedTypeIISelectedLabelDyadSum P Y M N α β F =
      ∑ a∈markedTypeIIOccupiedLabelEndpoints P Y M N,if a.label∣a.value-1 then
        markedTypeIIQuotientDampedCore P F ((a.value-1)/a.label)*
          markedTypeIILabelEndpointCoefficient P Y α β a else 0 := by
  unfold markedTypeIISelectedLabelDyadSum markedTypeIIOccupiedLabelEndpoints
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : markedTypeIILabelCutoff ((a.label:ℝ)/Y)=0
  · simp only [h,ne_eq,not_true_eq_false,ite_false,markedTypeIILabelEndpointCoefficient,mul_zero,zero_mul]
    split_ifs <;> rfl
  · rw [ite_eq_left h]

theorem markedTypeII_quotient_weight_reindex (E : Finset MarkedTypeIIEndpoint)
    (B : ℕ) (c : MarkedTypeIIEndpoint → ℂ) (F : ℕ → ℂ)
    (he : ∀ a∈E,0<a.label ∧ 1≤a.value ∧ a.value≤a.label*B) :
    (∑ a∈E,if a.label∣a.value-1 then F ((a.value-1)/a.label)*c a else 0)=
      ∑ h∈Finset.range B,F h*markedTypeIIEndpointSum E c h := by
  simp only [markedTypeIIEndpointSum,Finset.mul_sum,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hd : a.label∣a.value-1
  · rw [ite_eq_left hd]
    let h := (a.value-1)/a.label
    have hsub : a.value-1=a.label*h := (Nat.mul_div_cancel' hd).symm
    have hr : a.represents h := by
      unfold MarkedTypeIIEndpoint.represents
      have hv := (he a ha).2.1
      omega
    have hh : h∈Finset.range B := marked_quotient_mem_range_of_mul_bound hr (he a ha).2.2
    rw [Finset.sum_eq_single h]
    · rw [ite_eq_left hr]
    · intro j _ hj
      rw [ite_eq_right]
      intro hjr
      exact hj (marked_common_quotient_unique (he a ha).1 hjr hr)
    · exact fun hn => (hn hh).elim
  · rw [ite_eq_right hd]
    symm
    apply Finset.sum_eq_zero
    intro h _
    rw [ite_eq_right]
    intro hr
    apply hd
    exact ⟨h,by change a.value=1+a.label*h at hr; omega⟩

end
end ArtinMatthews
