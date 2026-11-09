module

public import ArtinMatthews.VaryingKummerAnalyticZeroHeightCard
public import ArtinMatthews.VaryingKummerAnalyticHeightAvoidance


set_option backward.privateInPublic true
@[expose] public section

/-! A contour height avoiding every zero, obtained from the actual finite
height window. Zeros outside the window are handled explicitly. -/
namespace OAI.PrimeDegreePackets.AnalyticGrowth
open ArtinMatthews.ReusedGrowth
open ArtinMatthews.VaryingKummerAnalytic
open Set Complex
noncomputable section

lemma zeroHeightWindow_outside_distance {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hfe : ∀ z, f (1-z) = f z)
    (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1) {T t : ℝ}
    (ht : t ∈ Icc T (T+1)) {ρ : ℂ} (hρ : f ρ = 0)
    (hout : ρ ∉ zeroHeightWindow f (T+1/2)) :
    (1/2 : ℝ) ≤ |t-ρ.im| := by
  have hfar : 1 < |T+1/2-ρ.im| := by
    apply lt_of_not_ge
    intro hh
    exact hout ((mem_zeroHeightWindow_iff hf h0 hfe hstrip (T+1/2) ρ).mpr ⟨hρ,hh⟩)
  have hcenter : |T+1/2-t| ≤ (1/2 : ℝ) := by
    apply abs_le.mpr
    constructor <;> linarith [ht.1,ht.2]
  have htri := abs_add_le (T+1/2-t) (t-ρ.im)
  have he : (T+1/2-t)+(t-ρ.im) = T+1/2-ρ.im := by ring
  rw [he] at htri
  linarith

theorem exists_zeroHeightCount_avoiding {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hfe : ∀ z, f (1-z) = f z)
    (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1) (T : ℝ) :
    ∃ t ∈ Icc T (T+1), ∀ ρ : ℂ, f ρ = 0 →
      1/(2*(zeroHeightCount f (T+1/2)+1)) ≤ |t-ρ.im| := by
  classical
  let S : Finset ℝ := (zeroHeightWindow f (T+1/2)).image Complex.im
  have hc : (S.card : ℝ) ≤ zeroHeightCount f (T+1/2) :=
    zeroHeightImaginary_card_le hf h0 hfe hstrip (T+1/2)
  have hn : 0 ≤ zeroHeightCount f (T+1/2) :=
    (Nat.cast_nonneg S.card).trans hc
  have hsmall : 1/(2*(zeroHeightCount f (T+1/2)+1)) ≤ 1/(2*((S.card : ℝ)+1)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hhalf : 1/(2*(zeroHeightCount f (T+1/2)+1)) ≤ (1/2 : ℝ) := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  obtain ⟨t,ht,havoid⟩ := exists_height_avoiding_finset S T
  refine ⟨t,ht,?_⟩
  intro ρ hρ
  by_cases hm : ρ ∈ zeroHeightWindow f (T+1/2)
  · exact hsmall.trans (havoid ρ.im (Finset.mem_image.mpr ⟨ρ,hm,rfl⟩))
  · exact hhalf.trans (zeroHeightWindow_outside_distance hf h0 hfe hstrip ht hρ hm)

end
end OAI.PrimeDegreePackets.AnalyticGrowth
