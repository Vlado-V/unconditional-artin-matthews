module

public import ArtinMatthews.ShiftedBesselDenominator
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension


set_option backward.privateInPublic true
@[expose] public section

/-! Actual compact source cutoffs for the original shifted correlation.
A fixed smooth plateau supplies the second cutoff. Its construction, support,
normalization, and affine derivative scaling are proved explicitly. -/

noncomputable section
open Complex Real Set Metric
open scoped ContDiff

namespace ArtinMatthews

private def sourcePlateauBump : ContDiffBump (3/2 : ℝ) where
  rIn := 1/2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- A fixed complex-valued smooth plateau, equal to one on [1,2]. -/
def shiftedSourcePlateau (x : ℝ) : ℂ := (sourcePlateauBump x : ℝ)

theorem shiftedSourcePlateau_smooth : ContDiff ℝ ∞ shiftedSourcePlateau := by
  exact Complex.ofRealCLM.contDiff.comp sourcePlateauBump.contDiff

theorem shiftedSourcePlateau_one (x : ℝ) (hx : x ∈ Icc 1 2) : shiftedSourcePlateau x = 1 := by
  have hb : x ∈ closedBall (3/2 : ℝ) sourcePlateauBump.rIn := by
    rw [mem_closedBall, Real.dist_eq, abs_le]
    change -(1/2 : ℝ) ≤ x-3/2 ∧ x-3/2 ≤ 1/2
    constructor <;> linarith [hx.1,hx.2]
  simp only [shiftedSourcePlateau, sourcePlateauBump.one_of_mem_closedBall hb, Complex.ofReal_one]

theorem shiftedSourcePlateau_support : Function.support shiftedSourcePlateau ⊆ Icc (1/2) (5/2) := by
  intro x hx
  change shiftedSourcePlateau x ≠ 0 at hx
  have hn : sourcePlateauBump x ≠ 0 := by simpa only [shiftedSourcePlateau, ne_eq, Complex.ofReal_eq_zero] using hx
  have hb : x ∈ ball (3/2 : ℝ) sourcePlateauBump.rOut := by
    rw [← sourcePlateauBump.support_eq]
    exact hn
  rw [mem_ball, Real.dist_eq, abs_lt] at hb
  change -(1 : ℝ) < x-3/2 ∧ x-3/2 < 1 at hb
  constructor <;> linarith [hb.1,hb.2]

theorem shiftedSourcePlateau_norm (x : ℝ) : ‖shiftedSourcePlateau x‖ ≤ 1 := by
  rw [shiftedSourcePlateau, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg sourcePlateauBump.nonneg]
  exact sourcePlateauBump.le_one

/-- The affine source test used in the first variable. -/
def shiftedSourceTest (g : ℝ → ℂ) (m : ℝ) (x : ℝ) : ℂ := g ((x-1)/m)

/-- The second test is fixed after rescaling by mT. -/
def shiftedSourceMajorant (m T : ℝ) (x : ℝ) : ℂ := shiftedSourcePlateau ((x-1)/(m*T))

theorem shiftedSourceTest_smooth (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (m : ℝ) :
    ContDiff ℝ ∞ (shiftedSourceTest g m) := by
  unfold shiftedSourceTest
  exact hg.comp (by fun_prop)

theorem shiftedSourceMajorant_smooth (m T : ℝ) : ContDiff ℝ ∞ (shiftedSourceMajorant m T) := by
  unfold shiftedSourceMajorant
  exact shiftedSourcePlateau_smooth.comp (by fun_prop)

/-- The original cutoff has its exact positive compact support after the shift. -/
theorem shiftedSourceTest_support (g : ℝ → ℂ) (T m : ℝ) (hm : 0 < m)
    (hg : Function.support g ⊆ Icc T (2*T)) :
    Function.support (shiftedSourceTest g m) ⊆ Icc (1+m*T) (1+2*m*T) := by
  intro x hx
  have h := hg hx
  change T ≤ (x-1)/m ∧ (x-1)/m ≤ 2*T at h
  constructor
  · have := (le_div_iff₀ hm).mp h.1
    nlinarith
  · have := (div_le_iff₀ hm).mp h.2
    nlinarith

theorem shiftedSourceMajorant_support (m T : ℝ) (hm : 0 < m) (hT : 0 < T) :
    Function.support (shiftedSourceMajorant m T) ⊆ Icc (1+m*T/2) (1+5*m*T/2) := by
  intro x hx
  have h := shiftedSourcePlateau_support hx
  change 1/2 ≤ (x-1)/(m*T) ∧ (x-1)/(m*T) ≤ 5/2 at h
  constructor
  · have := (le_div_iff₀ (mul_pos hm hT)).mp h.1
    nlinarith
  · have := (div_le_iff₀ (mul_pos hm hT)).mp h.2
    nlinarith

/-- Exact source factorization on the original shifted arguments. -/
theorem shiftedSourceTest_product (g : ℝ → ℂ) (T m1 m2 n : ℝ)
    (hT : 0 < T) (hm1 : 0 < m1) (hm2 : 0 < m2)
    (hg : Function.support g ⊆ Icc T (2*T)) :
    shiftedSourceTest g m1 (m1*n+1) * shiftedSourceMajorant m2 T (m2*n+1) = g n := by
  have h1 : (m1*n+1-1)/m1 = n := by field_simp; ring
  have h2 : (m2*n+1-1)/(m2*T) = n/T := by field_simp; ring
  simp only [shiftedSourceTest, shiftedSourceMajorant, h1, h2]
  by_cases hn : g n = 0
  · simp [hn]
  · have hb := hg hn
    have hnt : n/T ∈ Icc 1 2 := by
      constructor
      · exact (le_div_iff₀ hT).mpr (by simpa using hb.1)
      · exact (div_le_iff₀ hT).mpr (by simpa using hb.2)
    rw [shiftedSourcePlateau_one _ hnt, mul_one]

/-- Exact affine derivative scaling, before inserting a cutoff derivative bound. -/
theorem iteratedDeriv_shiftedSourceTest (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (m x : ℝ) (j : ℕ) :
    iteratedDeriv j (shiftedSourceTest g m) x =
      (m⁻¹^j) • iteratedDeriv j g ((x-1)/m) := by
  have he : shiftedSourceTest g m = fun z : ℝ ↦ (fun y : ℝ ↦ g (m⁻¹ • y)) (z-1) := by
    funext z
    simp only [shiftedSourceTest, smul_eq_mul, div_eq_inv_mul]
  rw [he, iteratedDeriv_comp_sub_const j (fun y : ℝ ↦ g (m⁻¹ • y)) 1]
  have hd := congrArg (fun h : ℝ → ℂ ↦ h (x-1))
    (iteratedDeriv_comp_const_smul (n := j) (hg.of_le (by simp)) m⁻¹)
  simpa only [smul_eq_mul, div_eq_inv_mul] using hd

/-- A prescribed T-scale derivative bound becomes the correct mT-scale
bound after inserting the shifted source test. -/
theorem shiftedSourceTest_derivative_bound (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (m T C : ℝ) (hm : 0 < m) (_hT : 0 < T) (j : ℕ)
    (hb : ∀ x : ℝ, ‖iteratedDeriv j g x‖ ≤ C/T^j) (x : ℝ) :
    ‖iteratedDeriv j (shiftedSourceTest g m) x‖ ≤ C/(m*T)^j := by
  rw [iteratedDeriv_shiftedSourceTest g hg m x j, norm_smul, Real.norm_eq_abs,
    abs_pow, abs_inv, abs_of_pos hm]
  have h := mul_le_mul_of_nonneg_left (hb ((x-1)/m)) (pow_nonneg (inv_nonneg.mpr hm.le) j)
  convert h using 1
  rw [mul_pow]
  ring

end ArtinMatthews
