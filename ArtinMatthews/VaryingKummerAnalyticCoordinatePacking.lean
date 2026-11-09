module

public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! Coordinate-grid packing in arbitrary finite dimension. This is the generic
version of the grid argument in the pinned OpenAI HuxleyGridPacking source;
there is no Eisenstein or number-field specialization in this file. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open scoped BigOperators
noncomputable section
variable {β ι : Type*} [Fintype β]

private theorem coordinate_same_floor_abs_sub_lt_one {x y : ℝ} (h : ⌊x⌋ = ⌊y⌋) :
    |x-y| < 1 := by
  have hx := Int.floor_le x
  have hy := Int.floor_le y
  have hx' := Int.lt_floor_add_one x
  have hy' := Int.lt_floor_add_one y
  rw [h] at hx hx'
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

def coordinateGrid (Q : ℝ) (z x : β → ℝ) : β → ℤ := fun b =>
  ⌊Q * (x b-z b)⌋

theorem coordinateGrid_close {Q : ℝ} (hQ : 0 < Q) {z x y : β → ℝ}
    (h : coordinateGrid Q z x = coordinateGrid Q z y) : ‖x-y‖ < 1/Q := by
  apply (pi_norm_lt_iff (one_div_pos.mpr hQ)).mpr
  intro b
  have hh := coordinate_same_floor_abs_sub_lt_one (congrFun h b)
  change |Q*(x b-z b)-Q*(y b-z b)| < 1 at hh
  rw [show Q*(x b-z b)-Q*(y b-z b) = Q*(x b-y b) by ring,
    abs_mul,abs_of_pos hQ] at hh
  simpa only [Pi.sub_apply,Real.norm_eq_abs] using
    (lt_div_iff₀ hQ).mpr (by simpa only [mul_comm] using hh)

theorem coordinateGrid_injOn {Q : ℝ} (hQ : 0 < Q) (z : β → ℝ)
    (S : Finset ι) (x : ι → β → ℝ)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1/Q ≤ ‖x i-x j‖) :
    Set.InjOn (fun i => coordinateGrid Q z (x i)) (↑S : Set ι) := by
  intro i hi j hj hij
  by_contra hne
  exact (not_lt_of_ge (hsep i hi j hj hne)) (coordinateGrid_close hQ hij)

private theorem coordinate_floor_scaled_in_box {A R x : ℝ} (hA : 0 ≤ A)
    (hx : |x| ≤ R) :
    ⌊A*x⌋ ∈ Finset.Icc (-⌈A*R⌉-1) (⌈A*R⌉+1) := by
  have hx' := abs_le.mp hx
  have hlo := mul_le_mul_of_nonneg_left hx'.1 hA
  have hhi := mul_le_mul_of_nonneg_left hx'.2 hA
  have hc := Int.le_ceil (A*R)
  have hf := Int.floor_le (A*x)
  have hf' := Int.lt_floor_add_one (A*x)
  apply Finset.mem_Icc.mpr
  constructor
  · have hh : ((-⌈A*R⌉-1:ℤ):ℝ) ≤ (⌊A*x⌋:ℝ) := by push_cast; nlinarith
    exact_mod_cast hh
  · have hh : (⌊A*x⌋:ℝ) ≤ ((⌈A*R⌉+1:ℤ):ℝ) := by push_cast; nlinarith
    exact_mod_cast hh

theorem coordinate_separated_ball_count {Q : ℝ} (hQ : 0 < Q) (z : β → ℝ)
    (R : ℝ) (hR : 0 ≤ R) (S : Finset ι) (x : ι → β → ℝ)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1/Q ≤ ‖x i-x j‖)
    (hball : ∀ i ∈ S, ‖x i-z‖ ≤ R) :
    (S.card:ℝ) ≤ (2*Q*R+5)^(Fintype.card β) := by
  classical
  let B : ℤ := ⌈Q*R⌉+1
  let T : Finset (β → ℤ) := Fintype.piFinset (fun _ => Finset.Icc (-B) B)
  have hlow : -B = -⌈Q*R⌉-1 := by dsimp [B]; ring
  have hmem : ∀ i ∈ S, coordinateGrid Q z (x i) ∈ T := by
    intro i hi
    apply Fintype.mem_piFinset.mpr
    intro b
    change ⌊Q*(x i b-z b)⌋ ∈ Finset.Icc (-B) B
    rw [hlow]
    exact coordinate_floor_scaled_in_box hQ.le
      ((show |x i b-z b| ≤ ‖x i-z‖ from norm_le_pi_norm (x i-z) b).trans (hball i hi))
  have hc : S.card ≤ T.card := Finset.card_le_card_of_injOn _ hmem (coordinateGrid_injOn hQ z S x hsep)
  have hB0 : 0 ≤ B := by
    dsimp [B]
    have hc0 : (0:ℤ) ≤ ⌈Q*R⌉ := Int.ceil_nonneg (by positivity)
    omega
  have hcard : ((Finset.Icc (-B) B).card:ℝ) = 2*(B:ℝ)+1 := by
    rw [Int.card_Icc,← Int.cast_natCast,Int.toNat_of_nonneg (by omega)]
    push_cast
    ring
  have hT : (T.card:ℝ) = (2*(B:ℝ)+1)^(Fintype.card β) := by
    simp only [T,Fintype.card_piFinset,Finset.prod_const,Finset.card_univ,Nat.cast_pow,hcard]
  have hB : (B:ℝ) ≤ Q*R+2 := by
    have hh := Int.ceil_lt_add_one (Q*R)
    dsimp [B]
    push_cast
    linarith
  have hbase : 2*(B:ℝ)+1 ≤ 2*Q*R+5 := by linarith
  have hbase0 : 0 ≤ 2*(B:ℝ)+1 := by exact_mod_cast (show (0:ℤ) ≤ 2*B+1 by omega)
  calc
    (S.card:ℝ) ≤ (T.card:ℝ) := by exact_mod_cast hc
    _ = _ := hT
    _ ≤ _ := pow_le_pow_left₀ hbase0 hbase _

end
end ArtinMatthews.VaryingKummerAnalytic
