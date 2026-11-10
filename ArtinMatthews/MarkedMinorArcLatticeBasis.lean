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

/-! Actual determinant-one completion and Euclidean parallel reduction of a
primitive sheared Dirichlet vector. -/
namespace ArtinMatthews

/-- A primitive integer vector has an actual positively oriented integer
completion whose sheared parallel component is at most half the first length. -/
theorem markedMinorShear_reduced_completion (α : ℝ) {Y : ℝ} (hY : 0 < Y)
    (h l : ℤ) (hl : 0 < l) (hc : IsCoprime h l) :
    ∃ a b : ℤ, h*b-l*a=1 ∧
      |((h : ℝ)+(l : ℝ)*α)*((a : ℝ)+(b : ℝ)*α)+((l : ℝ)/Y)*((b : ℝ)/Y)| ≤
        (((h : ℝ)+(l : ℝ)*α)^2+((l : ℝ)/Y)^2)/2 := by
  obtain ⟨c,d,hcd⟩ := hc
  let a₀ := -d
  let b₀ := c
  let s := (h : ℝ)+(l : ℝ)*α
  let t := (l : ℝ)/Y
  let q := s^2+t^2
  let u := (a₀ : ℝ)+(b₀ : ℝ)*α
  let v := (b₀ : ℝ)/Y
  have ht : 0 < t := div_pos (by exact_mod_cast hl) hY
  have hq : 0 < q := by dsimp [q]; nlinarith [sq_nonneg s]
  let k : ℤ := round ((s*u+t*v)/q)
  refine ⟨a₀-k*h,b₀-k*l,?_,?_⟩
  · dsimp [a₀,b₀]
    linear_combination hcd
  · have he : ((h : ℝ)+(l : ℝ)*α)*
          (((a₀-k*h : ℤ) : ℝ)+((b₀-k*l : ℤ) : ℝ)*α)+
          ((l : ℝ)/Y)*(((b₀-k*l : ℤ) : ℝ)/Y) =
          q*((s*u+t*v)/q-(k : ℝ)) := by
      dsimp [q,s,t,u,v]
      push_cast
      field_simp
      ring
    rw [he,abs_mul,abs_of_pos hq]
    exact (mul_le_mul_of_nonneg_left (abs_sub_round ((s*u+t*v)/q)) hq.le).trans_eq
      (by dsimp [q,s,t]; ring)

/-- Exact sheared determinant of an actual determinant-one completion. -/
theorem markedMinorShear_completion_determinant (α : ℝ) {Y : ℝ} (hY : Y ≠ 0)
    (h l a b : ℤ) (hd : h*b-l*a=1) :
    ((h : ℝ)+(l : ℝ)*α)*((b : ℝ)/Y)-
      ((l : ℝ)/Y)*((a : ℝ)+(b : ℝ)*α) = 1/Y := by
  have hdr : (h : ℝ)*b-(l : ℝ)*a=1 := by exact_mod_cast hd
  field_simp
  nlinarith

set_option maxHeartbeats 600000 in
/-- The true Euclidean length of the reduced complementary vector is
controlled by len/2+1/(Ylen), with no shortest-vector assumption. -/
theorem markedMinorShear_completion_length (α : ℝ) {Y : ℝ} (hY : 0 < Y)
    (h l a b : ℤ) (hl : 0 < l) (hd : h*b-l*a=1)
    (hparallel : |((h : ℝ)+(l : ℝ)*α)*((a : ℝ)+(b : ℝ)*α)+
      ((l : ℝ)/Y)*((b : ℝ)/Y)| ≤
      (((h : ℝ)+(l : ℝ)*α)^2+((l : ℝ)/Y)^2)/2) :
    markedMinorShearLength α Y a b ≤ markedMinorShearLength α Y h l/2+
      1/(Y*markedMinorShearLength α Y h l) := by
  let len := markedMinorShearLength α Y h l
  let otherLen := markedMinorShearLength α Y a b
  let s := (h : ℝ)+(l : ℝ)*α
  let t := (l : ℝ)/Y
  let u := (a : ℝ)+(b : ℝ)*α
  let v := (b : ℝ)/Y
  let d := s*u+t*v
  have ht : 0 < t := div_pos (by exact_mod_cast hl) hY
  have hlensq : len^2=s^2+t^2 := Real.sq_sqrt (by positivity)
  have hotherLensq : otherLen^2=u^2+v^2 := Real.sq_sqrt (by positivity)
  have hlen : 0 < len := by
    have hn : 0 ≤ len := Real.sqrt_nonneg _
    nlinarith [sq_nonneg s]
  have hotherLen : 0 ≤ otherLen := Real.sqrt_nonneg _
  have hdet : s*v-t*u=1/Y := markedMinorShear_completion_determinant α hY.ne' h l a b hd
  have henergy : len^2*otherLen^2=d^2+(1/Y)^2 := by
    rw [hlensq,hotherLensq,← hdet]
    dsimp [d]
    ring
  have hdot : |d| ≤ len^2/2 := by simpa only [hlensq] using hparallel
  have hdotsq : d^2 ≤ (len^2/2)^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg d) (by positivity : (0:ℝ)≤len^2/2)).mpr hdot
    simpa only [sq_abs] using hh
  have hprod : len*otherLen ≤ len^2/2+1/Y := by
    apply (sq_le_sq₀ (mul_nonneg hlen.le hotherLen) (by positivity)).mp
    nlinarith [one_div_pos.mpr hY]
  calc
    _ = (len*otherLen)/len := by dsimp [otherLen]; field_simp
    _ ≤ (len^2/2+1/Y)/len := div_le_div_of_nonneg_right hprod hlen.le
    _ = _ := by dsimp [len]; field_simp

end ArtinMatthews
