module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.Liouville

/-! Quantitative logarithmic derivative bound for a zero-free disk.
A normalized primitive of the logarithmic derivative reduces this to
Borel–Carathéodory and the first-derivative Cauchy estimate. -/

public section

namespace ArtinMatthews

open Complex Metric Set

private theorem independentDiskPrimitive
    {g : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hg : AnalyticOnNhd ℂ g (ball 0 r)) (hgn : ∀ w ∈ ball 0 r, g w ≠ 0) :
    ∃ H : ℂ → ℂ, H 0 = 0 ∧
      (∀ w ∈ ball 0 r, HasDerivAt H (deriv g w / g w) w) ∧
      ∀ w ∈ ball 0 r, Complex.exp (H w) * g 0 = g w := by
  have hd : DifferentiableOn ℂ (fun w => deriv g w / g w) (ball 0 r) := by
    intro w hw
    exact (((hg w hw).deriv.div (hg w hw) (hgn w hw)).differentiableAt).differentiableWithinAt
  obtain ⟨H, hH0, hH⟩ := hd.isExactOn_ball.with_val_at 0 0
  refine ⟨H, hH0, hH, ?_⟩
  let p : ℂ → ℂ := fun w => Complex.exp (-H w) * g w
  have hp (w : ℂ) (hw : w ∈ ball 0 r) : HasDerivAt p 0 w := by
    have hprod := ((hH w hw).neg.cexp).mul (hg w hw).differentiableAt.hasDerivAt
    convert hprod using 1
    field_simp [hgn w hw]
    ring
  have hconst (w : ℂ) (hw : w ∈ ball 0 r) : p w = g 0 := by
    have heq := isOpen_ball.is_const_of_deriv_eq_zero
      (convex_ball (0 : ℂ) r).isPreconnected
      (fun a ha => (hp a ha).differentiableAt.differentiableWithinAt)
      (fun a ha => (hp a ha).deriv) hw (mem_ball_self hr)
    simpa only [p, hH0, neg_zero, Complex.exp_zero, one_mul] using heq
  intro w hw
  calc
    Complex.exp (H w) * g 0 = Complex.exp (H w) * p w := by rw [hconst w hw]
    _ = g w := by
      simp only [p, ← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]

theorem independentDisk_logDeriv_bound
    {g : ℂ → ℂ} {r1 r B : ℝ} (hr1 : 0 < r1) (hr1r : r1 < r) (hB : 1 < B)
    (hg : AnalyticOnNhd ℂ g (ball 0 r)) (hgn : ∀ w ∈ ball 0 r, g w ≠ 0)
    (hg0 : 1 ≤ ‖g 0‖) (hb : ∀ w ∈ ball 0 r, ‖g w‖ ≤ B)
    {z : ℂ} (hz : z ∈ closedBall 0 r1) :
    ‖deriv g z / g z‖ ≤ (16 * r ^ 2 / (r - r1) ^ 3) * Real.log B := by
  have hr := hr1.trans hr1r
  have hBp := zero_lt_one.trans hB
  let M := Real.log B
  have hM : 0 < M := Real.log_pos hB
  obtain ⟨H, hH0, hH, hExp⟩ := independentDiskPrimitive hr hg hgn
  have hHd : DifferentiableOn ℂ H (ball 0 r) :=
    fun w hw => (hH w hw).differentiableAt.differentiableWithinAt
  have hre : MapsTo H (ball 0 r) {v | v.re ≤ M} := by
    intro w hw
    have hnorm := congrArg norm (hExp w hw)
    rw [norm_mul, Complex.norm_exp] at hnorm
    have hle : Real.exp (H w).re ≤ B :=
      (le_mul_of_one_le_right (Real.exp_pos _).le hg0).trans (hnorm.trans_le (hb w hw))
    exact Real.exp_le_exp.mp (by simpa only [M, Real.exp_log hBp] using hle)
  let d := (r - r1) / 2
  let s := (r + r1) / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have hs : s < r := by dsimp [s]; linarith
  have hs0 : 0 < s := by dsimp [s]; linarith
  have hsd : r - s = d := by dsimp [s, d]; ring
  have hzR : z ∈ ball (0 : ℂ) r := closedBall_subset_ball hr1r hz
  have hsubset : closedBall z d ⊆ closedBall 0 s := by
    intro w hw
    apply mem_closedBall.mpr
    calc
      dist w (0 : ℂ) ≤ dist w z + dist z 0 := dist_triangle _ _ _
      _ ≤ d + r1 := add_le_add (mem_closedBall.mp hw) (mem_closedBall.mp hz)
      _ = s := by dsimp [d, s]; ring
  have hcircle (w : ℂ) (hw : w ∈ sphere z d) : ‖H w‖ ≤ 2 * M * s / (r - s) := by
    have hws := hsubset (sphere_subset_closedBall hw)
    have hwR := closedBall_subset_ball hs hws
    have hnorm := mem_closedBall_zero_iff.mp hws
    refine (Complex.borelCaratheodory_zero hM hHd hre hr hwR hH0).trans ?_
    calc
      2 * M * ‖w‖ / (r - ‖w‖) ≤ 2 * M * s / (r - ‖w‖) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm (by positivity)) (by linarith)
      _ ≤ 2 * M * s / (r - s) :=
        div_le_div_of_nonneg_left (by positivity) (sub_pos.mpr hs) (by linarith)
  have hC := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hd
    (hHd.diffContOnCl_ball (hsubset.trans (closedBall_subset_ball hs))) hcircle
  rw [(hH z hzR).deriv] at hC
  have hgap : 0 < r - r1 := sub_pos.mpr hr1r
  have hcoef : 8 * r / (r - r1)^2 ≤ 16 * r^2 / (r - r1)^3 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc
      8 * r * (r - r1)^3 = (8 * r * (r - r1)) * (r - r1)^2 := by ring
      _ ≤ (16 * r^2) * (r - r1)^2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        calc
          8 * r * (r - r1) ≤ 8 * r * r := by gcongr; linarith
          _ ≤ 16 * r^2 := by nlinarith [sq_nonneg r]
  calc
    ‖deriv g z / g z‖ ≤ 2 * M * s / (r - s) / d := hC
    _ ≤ 2 * M * r / (r - s) / d := by gcongr
    _ = (8 * r / (r - r1)^2) * M := by
      rw [hsd]
      dsimp [d]
      field_simp
      ring
    _ ≤ (16 * r^2 / (r - r1)^3) * Real.log B :=
      mul_le_mul_of_nonneg_right hcoef hM.le

end ArtinMatthews
