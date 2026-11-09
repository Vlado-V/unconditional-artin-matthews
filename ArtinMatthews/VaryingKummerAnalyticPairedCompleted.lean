module

public import ArtinMatthews.VaryingKummerAnalyticComplexZeroPole


set_option backward.privateInPublic true
@[expose] public section

/-! The product of an actual completed function and its inverse-character
completion. A single inverse-character functional equation makes the product
self-reflecting; no self-reflection of either factor is assumed. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open ArtinMatthews.ReusedGrowth OAI.PrimeDegreePackets.AnalyticGrowth
open Complex
open scoped ComplexConjugate
noncomputable section

def pairedCompleted (F G : ℂ → ℂ) : ℂ → ℂ := fun s => F s * G s

variable {F G : ℂ → ℂ}

theorem pairedCompleted_entire (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) :
    Differentiable ℂ (pairedCompleted F G) := hF.mul hG

theorem pairedCompleted_hasSubquadraticGrowth
    (hF : HasSubquadraticGrowth F) (hG : HasSubquadraticGrowth G) :
    HasSubquadraticGrowth (pairedCompleted F G) := hF.mul hG

theorem pairedCompleted_functionalEquation {W : ℂ}
    (hfe : ∀ s, F s = W * G (1-s)) (s : ℂ) :
    pairedCompleted F G (1-s) = pairedCompleted F G s := by
  have hr : 1-(1-s) = s := by ring
  simp only [pairedCompleted, hfe (1-s), hfe s, hr]
  ring

theorem pairedCompleted_conj (hconj : ∀ s, G (conj s) = conj (F s)) (s : ℂ) :
    pairedCompleted F G (conj s) = conj (pairedCompleted F G s) := by
  have hF : F (conj s) = conj (G s) := by
    simpa only [starRingEnd_self_apply] using (congrArg conj (hconj (conj s))).symm
  simp only [pairedCompleted, hF, hconj s, map_mul]
  ring

theorem pairedCompleted_zero_iff (s : ℂ) :
    pairedCompleted F G s = 0 ↔ F s = 0 ∨ G s = 0 := mul_eq_zero

theorem pairedCompleted_ne_zero_iff (s : ℂ) :
    pairedCompleted F G s ≠ 0 ↔ F s ≠ 0 ∧ G s ≠ 0 := mul_ne_zero_iff

theorem pairedCompleted_ne_zero_right
    (hF : ∀ s : ℂ, 1 < s.re → F s ≠ 0)
    (hG : ∀ s : ℂ, 1 < s.re → G s ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    pairedCompleted F G s ≠ 0 := mul_ne_zero (hF s hs) (hG s hs)

theorem pairedCompleted_zero_strip {W : ℂ}
    (hfe : ∀ s, F s = W * G (1-s))
    (hF : ∀ s : ℂ, 1 < s.re → F s ≠ 0)
    (hG : ∀ s : ℂ, 1 < s.re → G s ≠ 0)
    {s : ℂ} (hs : pairedCompleted F G s = 0) : 0 ≤ s.re ∧ s.re ≤ 1 := by
  constructor
  · by_contra hn
    have hr : 1 < (1-s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
    exact pairedCompleted_ne_zero_right hF hG hr
      ((pairedCompleted_functionalEquation hfe s).trans hs)
  · by_contra hn
    exact pairedCompleted_ne_zero_right hF hG (lt_of_not_ge hn) hs

theorem pairedCompleted_logDeriv (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    {s : ℂ} (hFs : F s ≠ 0) (hGs : G s ≠ 0) :
    logDeriv (pairedCompleted F G) s = logDeriv F s + logDeriv G s := by
  exact logDeriv_fun_mul s hFs hGs (hF s) (hG s)

theorem pairedCompleted_logDeriv_right (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (hFr : ∀ s : ℂ, 1 < s.re → F s ≠ 0)
    (hGr : ∀ s : ℂ, 1 < s.re → G s ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    logDeriv (pairedCompleted F G) s = logDeriv F s + logDeriv G s :=
  pairedCompleted_logDeriv hF hG (hFr s hs) (hGr s hs)

theorem pairedCompleted_logDeriv_norm_le (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    {s : ℂ} (hFs : F s ≠ 0) (hGs : G s ≠ 0) {B C : ℝ}
    (hB : ‖logDeriv F s‖ ≤ B) (hC : ‖logDeriv G s‖ ≤ C) :
    ‖logDeriv (pairedCompleted F G) s‖ ≤ B+C := by
  rw [pairedCompleted_logDeriv hF hG hFs hGs]
  exact (norm_add_le _ _).trans (add_le_add hB hC)

theorem pairedCompleted_analyticOrderAt (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (s : ℂ) :
    analyticOrderAt (pairedCompleted F G) s = analyticOrderAt F s + analyticOrderAt G s :=
  analyticOrderAt_mul (hF.analyticAt s) (hG.analyticAt s)

theorem pairedCompleted_meromorphicOrderAt (hF : Differentiable ℂ F)
    (hG : Differentiable ℂ G) (s : ℂ) :
    meromorphicOrderAt (pairedCompleted F G) s =
      meromorphicOrderAt F s + meromorphicOrderAt G s :=
  meromorphicOrderAt_mul (hF.analyticAt s).meromorphicAt (hG.analyticAt s).meromorphicAt

theorem pairedCompleted_zeroMultiplicity (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (h0 : pairedCompleted F G 0 ≠ 0) (s : ℂ) :
    zeroMultiplicity (pairedCompleted F G) s = zeroMultiplicity F s + zeroMultiplicity G s := by
  obtain ⟨hF0,hG0⟩ := (pairedCompleted_ne_zero_iff 0).mp h0
  unfold zeroMultiplicity
  rw [pairedCompleted_meromorphicOrderAt hF hG s]
  exact WithTop.untop₀_add (entire_order_ne_top hF hF0 s) (entire_order_ne_top hG hG0 s)

end
end ArtinMatthews.VaryingKummerAnalytic
