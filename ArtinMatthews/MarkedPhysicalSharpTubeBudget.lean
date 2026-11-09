module

public import ArtinMatthews.MarkedPhysicalSharpLogBudget
public import ArtinMatthews.MarkedPhysicalMomentTube


set_option backward.privateInPublic true
@[expose] public section

/-! The literal relative-coordinate tube costs exp(C log(x)^.73).
Its radius uses the original d0*Y exponent .21 and moment length .5. -/
namespace ArtinMatthews
noncomputable section

def markedPhysicalSharpTubeCost (K A : ℝ) : ℝ := 8*(43+1024*K+A)

theorem markedPhysicalSharpTubeCost_nonneg {K A : ℝ} (hK : 0 ≤ K) (hA : 0 ≤ A) :
    0 ≤ markedPhysicalSharpTubeCost K A := by
  unfold markedPhysicalSharpTubeCost
  positivity

theorem markedPhysicalMomentTube_width_product {x : ℝ} (hlog : 1 ≤ Real.log x)
    (n : ℕ) {K H A : ℝ} (hK : 0 ≤ K) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hHhi : H ≤ Real.exp (A*(Real.log x)^(21/100:ℝ))) :
    2*(markedPhysicalMomentTubeRadius n K H:ℝ)+1 ≤
      (35+1024*K)*((n:ℝ)+1)*Real.exp (A*(Real.log x)^(21/100:ℝ)) := by
  have hL : 0 ≤ Real.log x := by linarith
  have he : 1 ≤ Real.exp (A*(Real.log x)^(21/100:ℝ)) :=
    Real.one_le_exp (mul_nonneg hA (Real.rpow_nonneg hL _))
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 16+512*(n:ℝ)*K*H by positivity)
  have hw : 2*(markedPhysicalMomentTubeRadius n K H:ℝ)+1 ≤ 35+1024*(n:ℝ)*K*H := by
    unfold markedPhysicalMomentTubeRadius
    linarith
  have hfirst : 35 ≤ 35*((n:ℝ)+1)*Real.exp (A*(Real.log x)^(21/100:ℝ)) := by
    have h1 := mul_le_mul_of_nonneg_right
      (show (1:ℝ) ≤ (n:ℝ)+1 by have hn := Nat.cast_nonneg n (α := ℝ); linarith)
      (zero_le_one.trans he)
    nlinarith
  have hsecond : 1024*(n:ℝ)*K*H ≤
      1024*K*((n:ℝ)+1)*Real.exp (A*(Real.log x)^(21/100:ℝ)) := by
    have h1 := mul_le_mul_of_nonneg_left hHhi (show 0 ≤ 1024*(n:ℝ)*K by positivity)
    have h2 := mul_le_mul_of_nonneg_right (show (n:ℝ) ≤ (n:ℝ)+1 by linarith)
      (show 0 ≤ 1024*K*Real.exp (A*(Real.log x)^(21/100:ℝ)) by positivity)
    nlinarith
  nlinarith

theorem markedPhysicalMomentTube_width_sharp {x : ℝ} (hlog : 1 ≤ Real.log x)
    {K H A : ℝ} (hK : 0 ≤ K) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hHhi : H ≤ Real.exp (A*(Real.log x)^(21/100:ℝ))) :
    2*(markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K H:ℝ)+1 ≤
      Real.exp ((43+1024*K+A)*(Real.log x)^(23/100:ℝ)) := by
  let C := 35+1024*K
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hp : 1 ≤ (Real.log x)^(23/100:ℝ) := Real.one_le_rpow hlog (by norm_num)
  have hc : C ≤ Real.exp (C*(Real.log x)^(23/100:ℝ)) := by
    have he : C ≤ Real.exp C := by linarith [Real.add_one_le_exp C]
    exact he.trans (Real.exp_le_exp.mpr (by nlinarith))
  have hs : Real.exp (A*(Real.log x)^(21/100:ℝ)) ≤
      Real.exp (A*(Real.log x)^(23/100:ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hlog (by norm_num : (21/100:ℝ) ≤ 23/100)) hA)
  calc
    _ ≤ C*((markedMemoryMomentLength x:ℝ)+1)*Real.exp (A*(Real.log x)^(21/100:ℝ)) :=
      markedPhysicalMomentTube_width_product hlog _ hK hH hA hHhi
    _ ≤ Real.exp (C*(Real.log x)^(23/100:ℝ))*
        Real.exp (8*(Real.log x)^(23/100:ℝ))*Real.exp (A*(Real.log x)^(23/100:ℝ)) :=
      mul_le_mul (mul_le_mul hc (markedPhysicalMomentLength_exp_sharp hlog)
        (by positivity) (Real.exp_nonneg _)) hs (Real.exp_nonneg _) (by positivity)
    _ = _ := by
      rw [← Real.exp_add,← Real.exp_add]
      congr 1
      dsimp [C]
      ring

theorem markedPhysicalMomentTube_path_sharp {x : ℝ} (hlog : 1 ≤ Real.log x)
    {K H A : ℝ} (hK : 0 ≤ K) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hHhi : H ≤ Real.exp (A*(Real.log x)^(21/100:ℝ))) :
    (2*(markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K H:ℝ)+1)^
        (2*markedMemoryMomentLength x) ≤
      Real.exp (markedPhysicalSharpTubeCost K A*(Real.log x)^(73/100:ℝ)) := by
  have hL : 0 < Real.log x := by linarith
  have hn : (markedMemoryMomentLength x:ℝ) ≤ 4*(Real.log x)^(1/2:ℝ) := by
    linarith [(markedMemoryMomentLength_sqrt_bound hlog).1]
  have hc : 0 ≤ 43+1024*K+A := by positivity
  have he : (Real.log x)^(1/2:ℝ)*(Real.log x)^(23/100:ℝ)=(Real.log x)^(73/100:ℝ) := by
    rw [← Real.rpow_add hL]
    norm_num
  have hcost : 2*(markedMemoryMomentLength x:ℝ)*((43+1024*K+A)*(Real.log x)^(23/100:ℝ)) ≤
      markedPhysicalSharpTubeCost K A*(Real.log x)^(73/100:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hn
      (show 0 ≤ 2*(43+1024*K+A)*(Real.log x)^(23/100:ℝ) by positivity)
    unfold markedPhysicalSharpTubeCost
    nlinarith
  calc
    _ ≤ (Real.exp ((43+1024*K+A)*(Real.log x)^(23/100:ℝ)))^(2*markedMemoryMomentLength x) :=
      pow_le_pow_left₀ (by positivity) (markedPhysicalMomentTube_width_sharp hlog hK hH hA hHhi) _
    _ = Real.exp (2*(markedMemoryMomentLength x:ℝ)*((43+1024*K+A)*(Real.log x)^(23/100:ℝ))) := by
      rw [← Real.exp_nat_mul]
      push_cast
      rfl
    _ ≤ _ := Real.exp_le_exp.mpr hcost

end
end ArtinMatthews
