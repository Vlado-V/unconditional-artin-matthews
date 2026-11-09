module

public import ArtinMatthews.SpectralBesselKWhittaker
public import ArtinMatthews.SpectralBesselKNonzero
public import Mathlib.Analysis.ODE.ExistUnique


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine initial-value uniqueness for the normal cusp Fourier equation. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectralSecondOrderField_lipschitz (a : ℂ) (M : ℝ≥0)
    (h1 : 1 ≤ (M : ℝ)) (ha : ‖a‖ ≤ (M : ℝ)) :
    LipschitzWith M (fun z : ℂ × ℂ => (z.2, a * z.1)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [dist_eq_norm, dist_eq_norm]
  change max ‖z.2 - w.2‖ ‖a * z.1 - a * w.1‖ ≤
    (M : ℝ) * max ‖z.1 - w.1‖ ‖z.2 - w.2‖
  apply max_le
  · calc
      _ ≤ max ‖z.1 - w.1‖ ‖z.2 - w.2‖ := le_max_right _ _
      _ ≤ _ := le_mul_of_one_le_left (le_trans (norm_nonneg _) (le_max_left _ _)) h1
  · rw [← mul_sub, norm_mul]
    exact mul_le_mul ha (le_max_left _ _) (norm_nonneg _) M.coe_nonneg

theorem spectralSecondOrder_unique_Ioo (a : ℝ → ℂ) (f g : ℝ → ℂ)
    (A B t₀ : ℝ) (M : ℝ≥0) (ht₀ : t₀ ∈ Ioo A B)
    (h1 : 1 ≤ (M : ℝ)) (ha : ∀ t ∈ Ioo A B, ‖a t‖ ≤ (M : ℝ))
    (hf : ∀ t ∈ Ioo A B, HasDerivAt f (deriv f t) t)
    (hf' : ∀ t ∈ Ioo A B, HasDerivAt (deriv f) (a t * f t) t)
    (hg : ∀ t ∈ Ioo A B, HasDerivAt g (deriv g t) t)
    (hg' : ∀ t ∈ Ioo A B, HasDerivAt (deriv g) (a t * g t) t)
    (hfg : f t₀ = g t₀) (hfg' : deriv f t₀ = deriv g t₀) :
    EqOn f g (Ioo A B) := by
  have he := ODE_solution_unique_of_mem_Ioo
    (v := fun t (z : ℂ × ℂ) => (z.2, a t * z.1))
    (s := fun _ => (univ : Set (ℂ × ℂ)))
    (f := fun t => (f t, deriv f t)) (g := fun t => (g t, deriv g t))
    (fun t ht => (spectralSecondOrderField_lipschitz (a t) M h1 (ha t ht)).lipschitzOnWith)
    ht₀ (fun t ht => ⟨(hf t ht).prodMk (hf' t ht), mem_univ _⟩)
    (fun t ht => ⟨(hg t ht).prodMk (hg' t ht), mem_univ _⟩)
    (Prod.ext hfg hfg')
  intro t ht
  exact congrArg Prod.fst (he ht)

theorem spectralNormalODE_unique (eig : ℂ) (q Y t₀ : ℝ) (hY : 0 ≤ Y)
    (ht₀ : Y < t₀) (f g : ℝ → ℂ)
    (hf : ∀ t, Y < t → HasDerivAt f (deriv f t) t)
    (hf' : ∀ t, Y < t → HasDerivAt (deriv f)
      (((q : ℂ) ^ 2 - eig / (t : ℂ) ^ 2) * f t) t)
    (hg : ∀ t, Y < t → HasDerivAt g (deriv g t) t)
    (hg' : ∀ t, Y < t → HasDerivAt (deriv g)
      (((q : ℂ) ^ 2 - eig / (t : ℂ) ^ 2) * g t) t)
    (hfg : f t₀ = g t₀) (hfg' : deriv f t₀ = deriv g t₀) :
    EqOn f g (Ioi Y) := by
  intro t ht
  let A := (Y + min t t₀) / 2
  let B := max t t₀ + 1
  have hmin : Y < min t t₀ := lt_min ht ht₀
  have hYA : Y < A := by dsimp [A]; linarith
  have hA : 0 < A := hY.trans_lt hYA
  have htAB : t ∈ Ioo A B := by
    constructor
    · dsimp [A]; linarith [min_le_left t t₀]
    · dsimp [B]; linarith [le_max_left t t₀]
  have ht₀AB : t₀ ∈ Ioo A B := by
    constructor
    · dsimp [A]; linarith [min_le_right t t₀]
    · dsimp [B]; linarith [le_max_right t t₀]
  let M : ℝ≥0 := ⟨1 + q ^ 2 + ‖eig‖ / A ^ 2, by positivity⟩
  have hM1 : 1 ≤ (M : ℝ) := by
    change 1 ≤ 1 + q ^ 2 + ‖eig‖ / A ^ 2
    have hd : 0 ≤ ‖eig‖ / A ^ 2 := by positivity
    nlinarith [sq_nonneg q]
  have hb : ∀ u ∈ Ioo A B, ‖(q : ℂ) ^ 2 - eig / (u : ℂ) ^ 2‖ ≤ (M : ℝ) := by
    intro u hu
    have hu0 : 0 < u := hA.trans hu.1
    have hs : A ^ 2 ≤ u ^ 2 := (sq_le_sq₀ hA.le hu0.le).mpr hu.1.le
    calc
      _ ≤ ‖(q : ℂ) ^ 2‖ + ‖eig / (u : ℂ) ^ 2‖ := norm_sub_le _ _
      _ = q ^ 2 + ‖eig‖ / u ^ 2 := by
        rw [norm_pow, norm_div, norm_pow, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, abs_of_pos hu0]
      _ ≤ q ^ 2 + ‖eig‖ / A ^ 2 := by
        have hd := div_le_div_of_nonneg_left (norm_nonneg eig) (sq_pos_of_pos hA) hs
        linarith
      _ ≤ _ := by
        change q ^ 2 + ‖eig‖ / A ^ 2 ≤ 1 + q ^ 2 + ‖eig‖ / A ^ 2
        linarith
  exact spectralSecondOrder_unique_Ioo
    (fun u => (q : ℂ) ^ 2 - eig / (u : ℂ) ^ 2) f g A B t₀ M ht₀AB hM1 hb
    (fun u hu => hf u (hYA.trans hu.1))
    (fun u hu => hf' u (hYA.trans hu.1))
    (fun u hu => hg u (hYA.trans hu.1))
    (fun u hu => hg' u (hYA.trans hu.1)) hfg hfg' htAB

theorem spectralKBesselWhittaker_normalODE (ν : ℂ) (q y : ℝ)
    (hq : 0 < q) (hy : 0 < y) :
    deriv (deriv (spectralKBesselWhittaker ν q)) y =
      ((q : ℂ) ^ 2 - (1 / 4 - ν ^ 2) / (y : ℂ) ^ 2) *
        spectralKBesselWhittaker ν q y := by
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have he := spectralKBesselWhittaker_fourierODE ν q y hq hy
  apply (mul_left_cancel₀ (pow_ne_zero 2 hy0))
  field_simp [hy0]
  linear_combination -4 * he

theorem spectralKBesselWhittaker_deriv_normal_hasDerivAt (ν : ℂ) (q y : ℝ)
    (hq : 0 < q) (hy : 0 < y) :
    HasDerivAt (deriv (spectralKBesselWhittaker ν q))
      (((q : ℂ) ^ 2 - (1 / 4 - ν ^ 2) / (y : ℂ) ^ 2) *
        spectralKBesselWhittaker ν q y) y := by
  have hd := spectralKBesselWhittaker_deriv_hasDerivAt ν q y hq hy
  rw [← spectralKBesselWhittaker_second_deriv ν q y hq hy,
    spectralKBesselWhittaker_normalODE ν q y hq hy] at hd
  exact hd

theorem spectralKBesselWhittaker_exists_ne_zero (ν : ℂ) (hν : -1 / 2 < ν.re)
    (q : ℝ) (hq : 0 < q) :
    ∃ y : ℝ, 0 < y ∧ spectralKBesselWhittaker ν q y ≠ 0 := by
  obtain ⟨x, hx, hK⟩ := schlafliBesselK_exists_ne_zero ν hν
  refine ⟨x / q, div_pos hx hq, ?_⟩
  rw [spectralKBesselWhittaker_eq_sqrt ν q (x / q) (div_pos hx hq).le,
    mul_div_cancel₀ x hq.ne']
  exact mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (div_pos hx hq))) hK

theorem spectralKBesselWhittaker_exists_ne_zero_above (ν : ℂ) (hν : -1 / 2 < ν.re)
    (q Y : ℝ) (hq : 0 < q) :
    ∃ y : ℝ, 0 < y ∧ Y < y ∧ spectralKBesselWhittaker ν q y ≠ 0 := by
  by_contra hn
  push Not at hn
  let a := max Y 0 + 1
  have ha : 0 < a := by dsimp [a]; linarith [le_max_right Y 0]
  have hYa : Y < a := by dsimp [a]; linarith [le_max_left Y 0]
  have hzero : spectralKBesselWhittaker ν q a = 0 := hn a ha hYa
  have hd0 : deriv (spectralKBesselWhittaker ν q) a = 0 := by
    have hd : HasDerivAt (spectralKBesselWhittaker ν q) 0 a := by
      apply (hasDerivAt_const a (0 : ℂ)).congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds ha, eventually_gt_nhds hYa] with y hy hyY
      exact hn y hy hyY
    exact hd.deriv
  have he := spectralNormalODE_unique (1 / 4 - ν ^ 2) q 0 a (le_refl 0) ha
    (spectralKBesselWhittaker ν q) (fun _ => (0 : ℂ))
    (fun y hy => by
      have hd := spectralKBesselWhittaker_hasDerivAt ν q y hq hy
      rw [← spectralKBesselWhittaker_deriv ν q y hq hy] at hd
      exact hd)
    (fun y hy => spectralKBesselWhittaker_deriv_normal_hasDerivAt ν q y hq hy)
    (fun y _ => by simpa only [deriv_const] using hasDerivAt_const y (0 : ℂ))
    (fun y _ => by
      have hz : deriv (fun _ : ℝ => (0 : ℂ)) = (fun _ => 0) := by funext t; simp
      rw [hz]
      simpa only [mul_zero] using hasDerivAt_const y (0 : ℂ))
    hzero (by simpa only [deriv_const] using hd0)
  obtain ⟨y, hy, hne⟩ := spectralKBesselWhittaker_exists_ne_zero ν hν q hq
  exact hne (he hy)

end ArtinMatthews
