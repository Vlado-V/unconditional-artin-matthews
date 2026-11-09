module

public import ArtinMatthews.MarkedLocalizedMomentRoots


set_option backward.privateInPublic true
@[expose] public section

/-! Exact scalar normalization of the source localized moment estimate.
The box-volume factors cancel before the moment root is taken. -/
namespace ArtinMatthews
noncomputable section

theorem markedPhysicalTypeII_moment_scalar
    (z B X L D G H : ℝ) (hz : 0 ≤ z) (hB : 0 ≤ B) (hX : 0 < X)
    (hL : 0 < L) (hH : 0 ≤ H) (k : ℕ)
    (h : z^(2*(k+1)) ≤ B^(k+1)*(32*X*L^D)^(k+1)*(32*X*L^D)^k*
      ((256*H+1)*L^D)*(X*L^(-G*(2*((k+1:ℕ):ℝ))))) :
    z ≤ 32*Real.sqrt B*(256*H+1)^((2*((k+1:ℕ):ℝ))⁻¹)*X*L^(D-G) := by
  let n : ℝ := 2*((k+1:ℕ):ℝ)
  let a : ℝ := 1/2
  let b : ℝ := (k:ℝ)/n
  let c : ℝ := n⁻¹
  let E := 32*X*L^D
  have hn : 0 < n := by dsimp [n]; positivity
  have he : 0 ≤ E := by dsimp [E]; positivity
  have hc : 0 ≤ c := inv_nonneg.mpr hn.le
  have habc : a+b+c=1 := by
    dsimp [a,b,c,n]
    push_cast
    field_simp
    ring
  have hnc : n*c=1 := mul_inv_cancel₀ hn.ne'
  have hcell : 0 ≤ 256*H+1 := by positivity
  have hr := markedLocalizedMoment_root_bound z B E E ((256*H+1)*L^D)
    (X*L^(-G*n)) hz hB he he (by positivity) (by positivity) k h
  change z ≤ Real.sqrt B*Real.sqrt E*E^b*((256*H+1)*L^D)^c*(X*L^(-G*n))^c at hr
  have hEpow (u : ℝ) : E^u=(32:ℝ)^u*X^u*L^(D*u) := by
    dsimp only [E]
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hL.le D),
      Real.mul_rpow (by norm_num : (0:ℝ) ≤ 32) hX.le,← Real.rpow_mul hL.le]
  have hCp : ((256*H+1)*L^D)^c=(256*H+1)^c*L^(D*c) := by
    rw [Real.mul_rpow hcell (Real.rpow_nonneg hL.le _),← Real.rpow_mul hL.le]
  have hTp : (X*L^(-G*n))^c=X^c*L^(-G) := by
    rw [Real.mul_rpow hX.le (Real.rpow_nonneg hL.le _),← Real.rpow_mul hL.le]
    congr 2
    calc
      (-G*n)*c=-G*(n*c) := by ring
      _ = -G := by rw [hnc,mul_one]
  rw [Real.sqrt_eq_rpow E,hEpow a,hEpow b,hCp,hTp] at hr
  have hXp : X^a*X^b*X^c=X := by
    rw [← Real.rpow_add hX,← Real.rpow_add hX,habc,Real.rpow_one]
  have hLp : L^(D*a)*L^(D*b)*L^(D*c)*L^(-G)=L^(D-G) := by
    rw [← Real.rpow_add hL,← Real.rpow_add hL,← Real.rpow_add hL]
    congr 1
    calc
      D*a+D*b+D*c+-G=D*(a+b+c)-G := by ring
      _ = D-G := by rw [habc,mul_one]
  have h32 : (32:ℝ)^a*(32:ℝ)^b ≤ 32 := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 32)]
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 32)
      (show a+b ≤ 1 by linarith)).trans_eq (Real.rpow_one 32)
  have hid : Real.sqrt B*((32:ℝ)^a*X^a*L^(D*a))*((32:ℝ)^b*X^b*L^(D*b))*
      ((256*H+1)^c*L^(D*c))*(X^c*L^(-G)) =
      ((32:ℝ)^a*(32:ℝ)^b)*(Real.sqrt B*(256*H+1)^c*X*L^(D-G)) := by
    calc
      _ = ((32:ℝ)^a*(32:ℝ)^b)*(Real.sqrt B*(256*H+1)^c*
          (X^a*X^b*X^c)*(L^(D*a)*L^(D*b)*L^(D*c)*L^(-G))) := by ring
      _ = _ := by rw [hXp,hLp]
  rw [hid] at hr
  apply hr.trans
  have hp := mul_le_mul_of_nonneg_right h32
    (show 0 ≤ Real.sqrt B*(256*H+1)^c*X*L^(D-G) by positivity)
  dsimp only [c,n] at hp
  nlinarith

end
end ArtinMatthews
