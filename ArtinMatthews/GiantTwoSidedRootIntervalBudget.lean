module

public import ArtinMatthews.GiantTwoSidedRootMargin


set_option backward.privateInPublic true
@[expose] public section

/-! The literal ceiling interval has a positive lower endpoint and
enough integer roots for the relative CRT estimate. -/
namespace ArtinMatthews
open Filter
noncomputable section

theorem giantTwoSidedRootInterval_lower_endpoint {X : ℝ} (hX : 0<X) : 1≤⌈X⌉₊ :=
  Nat.ceil_pos.mpr hX

theorem giantTwoSidedRootInterval_length {X : ℝ} (hX : 2≤X) :
    X/2≤((⌈2*X⌉₊-⌈X⌉₊:ℕ):ℝ) := by
  have hX0 : 0≤X := zero_le_two.trans hX
  have hc : ⌈X⌉₊≤⌈2*X⌉₊ := Nat.ceil_mono (by linarith)
  rw [Nat.cast_sub hc]
  have hlo := Nat.le_ceil (2*X)
  have hhi := (Nat.ceil_lt_add_one hX0).le
  linarith

theorem giantCandidateRootInterval_budget {γ : ℝ} (hγ : 0<γ) :
    ∀ᶠ x : ℝ in atTop,∀ X : ℝ,x^γ≤X →
      1≤⌈X⌉₊ ∧ Real.exp ((γ/2)*Real.log x)≤((⌈2*X⌉₊-⌈X⌉₊:ℕ):ℝ) := by
  have hγ2 : 0<γ/2 := half_pos hγ
  filter_upwards [eventually_gt_atTop (0:ℝ),
    (tendsto_rpow_atTop hγ2).eventually_ge_atTop (2:ℝ)] with x hx hlarge
  intro X hX
  have hpow : x^γ=(x^(γ/2))^2 := by
    rw [sq,← Real.rpow_add hx]
    congr 1
    ring
  have hX2 : 2≤X := by rw [hpow] at hX; nlinarith
  have hmid : x^(γ/2)≤X/2 := by
    rw [hpow] at hX
    have hmul := mul_le_mul_of_nonneg_right hlarge (zero_le_two.trans hlarge)
    nlinarith only [hX,hmul]
  refine ⟨giantTwoSidedRootInterval_lower_endpoint (zero_lt_two.trans_le hX2),?_⟩
  have he : Real.exp ((γ/2)*Real.log x)=x^(γ/2) := by
    rw [Real.rpow_def_of_pos hx,mul_comm]
  rw [he]
  exact hmid.trans (giantTwoSidedRootInterval_length hX2)

end
end ArtinMatthews
