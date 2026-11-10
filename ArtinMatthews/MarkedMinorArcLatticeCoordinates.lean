module

public import ArtinMatthews.MarkedMinorArcLatticeVector
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

/-! Exact integer basis coordinates and bounds on the actual sheared region. -/
namespace ArtinMatthews

/-- Coordinates in the determinant-one integer basis with columns (h,l),(a,b). -/
def markedMinorBasisCoords (h l a b : ℤ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (b*p.1-a*p.2,h*p.2-l*p.1)

theorem markedMinorBasisCoords_inverse (h l a b : ℤ) (hd : h*b-l*a=1) (p : ℤ × ℤ) :
    (markedMinorBasisCoords h l a b p).1*h+(markedMinorBasisCoords h l a b p).2*a=p.1 ∧
    (markedMinorBasisCoords h l a b p).1*l+(markedMinorBasisCoords h l a b p).2*b=p.2 := by
  constructor
  · dsimp [markedMinorBasisCoords]
    linear_combination p.1*hd
  · dsimp [markedMinorBasisCoords]
    linear_combination p.2*hd

theorem markedMinorBasisCoords_injective (h l a b : ℤ) (hd : h*b-l*a=1) :
    Function.Injective (markedMinorBasisCoords h l a b) := by
  intro p q hpq
  have hp := markedMinorBasisCoords_inverse h l a b hd p
  have hq := markedMinorBasisCoords_inverse h l a b hd q
  rw [hpq] at hp
  exact Prod.ext (hp.1.symm.trans hq.1) (hp.2.symm.trans hq.2)

/-- Positive orientation preserves the actual determinant of every pair. -/
theorem markedMinorBasisCoords_determinant (h l a b : ℤ) (hd : h*b-l*a=1)
    (p q : ℤ × ℤ) :
    (markedMinorBasisCoords h l a b p).1*(markedMinorBasisCoords h l a b q).2-
      (markedMinorBasisCoords h l a b p).2*(markedMinorBasisCoords h l a b q).1 =
      p.1*q.2-p.2*q.1 := by
  dsimp [markedMinorBasisCoords]
  linear_combination (p.1*q.2-p.2*q.1)*hd

/-- Dirichlet's short vector satisfies the exact scale used for the reduced
complement, independent of all good-state band parameters. -/
theorem markedMinorShearLength_scale {α Y : ℝ} (hY : 0 < Y) (h l : ℤ)
    (hupper : markedMinorShearLength α Y h l ≤ 2*Y^(-1/2 : ℝ)) :
    Y*(markedMinorShearLength α Y h l)^2 ≤ 4 := by
  have hn : 0 ≤ markedMinorShearLength α Y h l := Real.sqrt_nonneg _
  have hs := (sq_le_sq₀ hn (by positivity)).mpr hupper
  have he : (Y^(-1/2 : ℝ))^2 = Y^(-1 : ℝ) := by
    rw [← Real.rpow_mul_natCast hY.le]
    congr 1
    norm_num
  calc
    _ ≤ Y*(2*Y^(-1/2 : ℝ))^2 := mul_le_mul_of_nonneg_left hs hY.le
    _ = 4 := by rw [mul_pow,he,Real.rpow_neg_one]; field_simp; norm_num

/-- A reduced complementary vector is actually O(1/(Y*len)); no shortest
vector hypothesis is needed. -/
theorem markedMinorShear_completion_short {α Y : ℝ} (hY : 0 < Y)
    (h l a b : ℤ) (hlen : 0 < markedMinorShearLength α Y h l)
    (hscale : Y*(markedMinorShearLength α Y h l)^2 ≤ 4)
    (hcomp : markedMinorShearLength α Y a b ≤ markedMinorShearLength α Y h l/2+
      1/(Y*markedMinorShearLength α Y h l)) :
    markedMinorShearLength α Y a b ≤ 3/(Y*markedMinorShearLength α Y h l) := by
  apply (le_div_iff₀ (mul_pos hY hlen)).mpr
  calc
    _ ≤ (markedMinorShearLength α Y h l/2+1/(Y*markedMinorShearLength α Y h l))*
        (Y*markedMinorShearLength α Y h l) :=
      mul_le_mul_of_nonneg_right hcomp (by positivity)
    _ = Y*(markedMinorShearLength α Y h l)^2/2+1 := by field_simp
    _ ≤ _ := by linarith

private theorem minor_plane_det_bound {x₁ x₂ y₁ y₂ C R : ℝ}
    (hC : 0 ≤ C) (_hR : 0 ≤ R) (hx₁ : |x₁| ≤ C) (hx₂ : |x₂| ≤ C)
    (hy₁ : |y₁| ≤ R) (hy₂ : |y₂| ≤ R) : |x₁*y₂-x₂*y₁| ≤ 2*C*R := by
  calc
    _ ≤ |x₁*y₂|+|x₂*y₁| := abs_sub _ _
    _ = |x₁| * |y₂| + |x₂| * |y₁| := by rw [abs_mul,abs_mul]
    _ ≤ C*R+C*R := add_le_add
      (mul_le_mul hx₁ hy₂ (abs_nonneg _) hC) (mul_le_mul hx₂ hy₁ (abs_nonneg _) hC)
    _ = _ := by ring

/-- Every actual integer point in the source sheared region has the required
coordinate bounds in the positively oriented reduced basis. -/
theorem markedMinorBasisCoords_bounds {α Y C : ℝ} (hY : 0 < Y) (hC : 0 ≤ C)
    (h l a b : ℤ) (hlen : 0 < markedMinorShearLength α Y h l)
    (hcomp : markedMinorShearLength α Y a b ≤ 3/(Y*markedMinorShearLength α Y h l))
    (p : ℤ × ℤ) (hx : |(p.1 : ℝ)+(p.2 : ℝ)*α| ≤ C) (hy : |(p.2 : ℝ)/Y| ≤ C) :
    |((markedMinorBasisCoords h l a b p).1 : ℝ)| ≤ 6*C/markedMinorShearLength α Y h l ∧
    |((markedMinorBasisCoords h l a b p).2 : ℝ)| ≤ 2*C*Y*markedMinorShearLength α Y h l := by
  have hc₁ := markedMinorShearLength_coordinates α Y h l
  have hc₂ := markedMinorShearLength_coordinates α Y a b
  have hn₂ : 0 ≤ markedMinorShearLength α Y a b := Real.sqrt_nonneg _
  have he₁ : ((markedMinorBasisCoords h l a b p).1 : ℝ) =
      Y*(((p.1 : ℝ)+(p.2 : ℝ)*α)*((b : ℝ)/Y)-
        ((p.2 : ℝ)/Y)*((a : ℝ)+(b : ℝ)*α)) := by
    dsimp [markedMinorBasisCoords]
    push_cast
    field_simp
    ring
  have he₂ : ((markedMinorBasisCoords h l a b p).2 : ℝ) =
      Y*(((h : ℝ)+(l : ℝ)*α)*((p.2 : ℝ)/Y)-
        ((l : ℝ)/Y)*((p.1 : ℝ)+(p.2 : ℝ)*α)) := by
    dsimp [markedMinorBasisCoords]
    push_cast
    field_simp
    ring
  constructor
  · rw [he₁,abs_mul,abs_of_pos hY]
    calc
      _ ≤ Y*(2*C*markedMinorShearLength α Y a b) := mul_le_mul_of_nonneg_left
        (minor_plane_det_bound hC hn₂ hx hy hc₂.1 hc₂.2) hY.le
      _ ≤ Y*(2*C*(3/(Y*markedMinorShearLength α Y h l))) := by gcongr
      _ = _ := by field_simp; ring
  · rw [he₂,abs_mul,abs_of_pos hY]
    have hh := minor_plane_det_bound hlen.le hC hc₁.1 hc₁.2 hx hy
    nlinarith [mul_le_mul_of_nonneg_left hh hY.le]

end ArtinMatthews
