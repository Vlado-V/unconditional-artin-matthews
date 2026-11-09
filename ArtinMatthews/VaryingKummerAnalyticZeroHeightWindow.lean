module

public import ArtinMatthews.VaryingKummerAnalyticComplexZeroCount


set_option backward.privateInPublic true
@[expose] public section

/-! A concrete finite set containing exactly the zeros in a unit height
window, and the corresponding multiplicity count. -/
namespace OAI.PrimeDegreePackets.AnalyticGrowth

open ArtinMatthews.ReusedGrowth
open Complex
open scoped BigOperators
noncomputable section

/-- All zeros whose imaginary part is within one of T. The disk is large
enough for the entire critical strip in this height window. -/
def zeroHeightWindow (f : ℂ → ℂ) (T : ℝ) : Finset ℂ :=
  (zeroDiskFinset f (|T|+2)).filter (fun ρ => |T-ρ.im| ≤ 1)

lemma zero_in_height_window_norm_le {ρ : ℂ} {T : ℝ}
    (hρ₀ : 0 ≤ ρ.re) (hρ₁ : ρ.re ≤ 1) (hT : |T-ρ.im| ≤ 1) :
    ‖ρ‖ ≤ |T|+2 := by
  have him : |ρ.im| ≤ |T|+1 := by
    have H := abs_le.mp hT
    apply abs_le.mpr
    constructor <;> linarith [le_abs_self T, neg_le_abs T]
  have H := Complex.norm_le_abs_re_add_abs_im ρ
  rw [abs_of_nonneg hρ₀] at H
  linarith

lemma mem_zeroHeightWindow_iff {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hfe : ∀ z, f (1-z) = f z)
    (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1) (T : ℝ) (ρ : ℂ) :
    ρ ∈ zeroHeightWindow f T ↔ f ρ = 0 ∧ |T-ρ.im| ≤ 1 := by
  classical
  rw [zeroHeightWindow,Finset.mem_filter]
  constructor
  · rintro ⟨hm,hT⟩
    refine ⟨?_,hT⟩
    apply (zeroMultiplicity_ne_zero_iff hf h0 ρ).mp
    have H := (mem_zeroDiskFinset f (|T|+2) ρ).mp hm
    rwa [divisor_closedBall_eq_multiplicity hf (zeroDiskFinset_norm_le hm)] at H
  · rintro ⟨hz,hT⟩
    refine ⟨?_,hT⟩
    have hr := hstrip ρ hz
    have hl := hstrip (1-ρ) (by rwa [hfe])
    have hρ₀ : 0 ≤ ρ.re := by
      simp only [Complex.sub_re,Complex.one_re] at hl
      linarith
    rw [mem_zeroDiskFinset,divisor_closedBall_eq_multiplicity hf
      (zero_in_height_window_norm_le hρ₀ hr hT)]
    exact (zeroMultiplicity_ne_zero_iff hf h0 ρ).mpr hz

/-- Multiplicity is retained, including repeated zeros. -/
def zeroHeightCount (f : ℂ → ℂ) (T : ℝ) : ℝ :=
  ∑ ρ ∈ zeroHeightWindow f T, (zeroMultiplicity f ρ : ℝ)

theorem zeroHeightCount_le_logDeriv {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hg : HasSubquadraticGrowth f) (hfe : ∀ z, f (1-z) = f z)
    (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1) (T : ℝ) :
    zeroHeightCount f T ≤ 5*(logDeriv f (⟨2,T⟩ : ℂ)).re := by
  apply finite_zero_height_window_bound hf h0 hg hfe hstrip
  intro ρ hρ
  exact (Finset.mem_filter.mp hρ).2

end
end OAI.PrimeDegreePackets.AnalyticGrowth
