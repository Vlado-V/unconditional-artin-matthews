module

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real


set_option backward.privateInPublic true
@[expose] public section

/-! The source relation nX <= LG puts all three spectral factor products
in the same quantitative shape. The principal factor retains sqrt Z. -/
namespace ArtinMatthews
noncomputable section

def spectralABLSourceJoinConstant : ℝ := 1+4*Real.pi

private theorem join_constant_one_le : 1 ≤ spectralABLSourceJoinConstant := by
  unfold spectralABLSourceJoinConstant
  linarith [Real.pi_pos]

private theorem source_sqrt_pair_le
    {S U V C k₁ k₂ A D : ℝ}
    (hS : 0 ≤ S) (hU : 0 ≤ U) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hk₁ : 0 ≤ k₁) (hk₂ : 0 ≤ k₂) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hu : U ≤ C*k₁*A) (hv : V ≤ C*k₂*D) :
    Real.sqrt (S*U)*Real.sqrt V ≤
      C*Real.sqrt (k₁*k₂)*Real.sqrt S*Real.sqrt A*Real.sqrt D := by
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  calc
    _ = S*(U*V) := by
      rw [mul_pow,Real.sq_sqrt (mul_nonneg hS hU),Real.sq_sqrt hV]
      ring
    _ ≤ S*((C*k₁*A)*(C*k₂*D)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hu hv hV (by positivity)) hS
    _ = _ := by
      simp only [mul_pow,Real.sq_sqrt (mul_nonneg hk₁ hk₂),
        Real.sq_sqrt hS,Real.sq_sqrt hA,Real.sq_sqrt hD]
      ring

private theorem source_factor_bounds
    {Z R N n G X L : ℝ}
    (hZ : 1 ≤ Z) (hR : 0 ≤ R) (hN : 0 < N) (hn : 0 ≤ n)
    (hG : 0 ≤ G) (hX : 0 < X) (hL : 1 ≤ L) (hnX : n*X ≤ L*G) :
    let C := spectralABLSourceJoinConstant
    let A := Z^2+R/N
    let D := Z^2+G*Z/(X*N)
    (Z^2+4*Real.pi*R*Z/N ≤ C*Z*A) ∧
    (1+4*Real.pi*R/N ≤ C*A) ∧
    (Z^2+2*Real.pi*n*Z/N ≤ C*L*D) ∧
    (1+n/N ≤ C*L*D) := by
  let C := spectralABLSourceJoinConstant
  let A := Z^2+R/N
  let d := G*Z/(X*N)
  let D := Z^2+d
  have hC : 1 ≤ C := join_constant_one_le
  have hC₄ : 4*Real.pi ≤ C := by dsimp [C,spectralABLSourceJoinConstant]; linarith
  have hC₂ : 2*Real.pi ≤ C := by
    dsimp [C,spectralABLSourceJoinConstant]
    linarith [Real.pi_pos]
  have hZ₀ : 0 ≤ Z := zero_le_one.trans hZ
  have hL₀ : 0 ≤ L := zero_le_one.trans hL
  have hZsq : 1 ≤ Z^2 := one_le_pow₀ hZ
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hCZ : 1 ≤ C*Z := one_le_mul_of_one_le_of_one_le hC hZ
  have hCL : 1 ≤ C*L := one_le_mul_of_one_le_of_one_le hC hL
  have hfirst : Z^2+4*Real.pi*R*Z/N ≤ C*Z*A := by
    have hz := le_mul_of_one_le_left (sq_nonneg Z) hCZ
    have hr := mul_le_mul_of_nonneg_right hC₄
      (mul_nonneg (div_nonneg hR hN.le) hZ₀)
    calc
      _ = Z^2+(4*Real.pi)*(R/N*Z) := by ring
      _ ≤ C*Z*Z^2+C*(R/N*Z) := add_le_add hz hr
      _ = _ := by dsimp [A]; ring
  have hfirst₁ : 1+4*Real.pi*R/N ≤ C*A := by
    have hz := one_le_mul_of_one_le_of_one_le hC hZsq
    have hr := mul_le_mul_of_nonneg_right hC₄ (div_nonneg hR hN.le)
    calc
      _ = 1+(4*Real.pi)*(R/N) := by ring
      _ ≤ C*Z^2+C*(R/N) := add_le_add hz hr
      _ = _ := by dsimp [A]; ring
  have hn' : n ≤ L*G/X := (le_div_iff₀ hX).mpr hnX
  have hnt : n*Z/N ≤ L*d := by
    calc
      _ ≤ (L*G/X)*Z/N := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hn' hZ₀) hN.le
      _ = _ := by dsimp [d]; ring
  have hsecond : Z^2+2*Real.pi*n*Z/N ≤ C*L*D := by
    have hz := le_mul_of_one_le_left (sq_nonneg Z) hCL
    have ht := (mul_le_mul_of_nonneg_left hnt (by positivity : 0 ≤ 2*Real.pi)).trans
      (mul_le_mul_of_nonneg_right hC₂ (mul_nonneg hL₀ hd))
    calc
      _ = Z^2+(2*Real.pi)*(n*Z/N) := by ring
      _ ≤ C*L*Z^2+C*(L*d) := add_le_add hz ht
      _ = _ := by dsimp [D]; ring
  have hcoef : 1 ≤ 2*Real.pi*Z := one_le_mul_of_one_le_of_one_le
    (by linarith [Real.pi_gt_three]) hZ
  have hnt₁ : n/N ≤ (2*Real.pi)*(n*Z/N) := by
    have hh := le_mul_of_one_le_left (div_nonneg hn hN.le) hcoef
    convert hh using 1 <;> ring
  have hsecond₁ : 1+n/N ≤ C*L*D := by
    calc
      _ ≤ Z^2+(2*Real.pi)*(n*Z/N) := add_le_add hZsq hnt₁
      _ = Z^2+2*Real.pi*n*Z/N := by ring
      _ ≤ _ := hsecond
  exact ⟨hfirst,hfirst₁,hsecond,hsecond₁⟩

theorem spectralABL_source_principal_size
    {S Z R N n G X L : ℝ}
    (hS : 0 ≤ S) (hZ : 1 ≤ Z) (hR : 0 ≤ R) (hN : 0 < N) (hn : 0 ≤ n)
    (hG : 0 ≤ G) (hX : 0 < X) (hL : 1 ≤ L) (hnX : n*X ≤ L*G) :
    Real.sqrt (S*(Z^2+4*Real.pi*R*Z/N))*Real.sqrt (Z^2+2*Real.pi*n*Z/N) ≤
      spectralABLSourceJoinConstant*Real.sqrt (Z*L)*Real.sqrt S*
        Real.sqrt (Z^2+R/N)*Real.sqrt (Z^2+G*Z/(X*N)) := by
  have hb := source_factor_bounds hZ hR hN hn hG hX hL hnX
  exact source_sqrt_pair_le hS (by positivity) (by positivity)
    (zero_le_one.trans join_constant_one_le) (zero_le_one.trans hZ)
    (zero_le_one.trans hL) (by positivity) (by positivity) hb.1 hb.2.2.1

theorem spectralABL_source_holomorphic_size
    {S Z R N n G X L : ℝ}
    (hS : 0 ≤ S) (hZ : 1 ≤ Z) (hR : 0 ≤ R) (hN : 0 < N) (hn : 0 ≤ n)
    (hG : 0 ≤ G) (hX : 0 < X) (hL : 1 ≤ L) (hnX : n*X ≤ L*G) :
    Real.sqrt (S*(1+4*Real.pi*R/N))*Real.sqrt (1+n/N) ≤
      spectralABLSourceJoinConstant*Real.sqrt L*Real.sqrt S*
        Real.sqrt (Z^2+R/N)*Real.sqrt (Z^2+G*Z/(X*N)) := by
  have hb := source_factor_bounds hZ hR hN hn hG hX hL hnX
  simpa only [one_mul,mul_one] using source_sqrt_pair_le hS (by positivity) (by positivity)
    (zero_le_one.trans join_constant_one_le) (by norm_num : (0 : ℝ) ≤ 1)
    (zero_le_one.trans hL) (by positivity) (by positivity) (by simpa only [mul_one] using hb.2.1) hb.2.2.2

theorem spectralABL_source_complementary_size
    {S Z R N n G X L P ε : ℝ}
    (hS : 0 ≤ S) (hZ : 1 ≤ Z) (hR : 0 ≤ R) (hN : 0 < N) (hn : 0 ≤ n)
    (hG : 0 ≤ G) (hX : 0 < X) (hL : 1 ≤ L) (hnX : n*X ≤ L*G)
    (hP : 1 ≤ P) (hε : 0 ≤ ε)
    (hpow : (N*n/(X/Z))^ε ≤ P^(3*ε)) :
    Real.sqrt (S*(1+4*Real.pi*R/N))*
        Real.sqrt (1+(N*n/(X/Z))^ε*G/(N*(X/Z))) ≤
      spectralABLSourceJoinConstant*P^(3*ε/2)*Real.sqrt S*
        Real.sqrt (Z^2+R/N)*Real.sqrt (Z^2+G*Z/(X*N)) := by
  have hb := source_factor_bounds hZ hR hN hn hG hX hL hnX
  let d := G*Z/(X*N)
  let w := P^(3*ε)
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hw : 1 ≤ w := Real.one_le_rpow hP (by positivity)
  have hZsq : 1 ≤ Z^2 := one_le_pow₀ hZ
  have hden : G/(N*(X/Z)) = d := by
    dsimp [d]
    have hZ₀ : 0 < Z := zero_lt_one.trans_le hZ
    field_simp [hN.ne',hX.ne',hZ₀.ne']
  have hv : 1+(N*n/(X/Z))^ε*G/(N*(X/Z)) ≤
      spectralABLSourceJoinConstant*w*(Z^2+d) := by
    rw [mul_div_assoc,hden]
    calc
      _ ≤ w*Z^2+w*d := add_le_add (one_le_mul_of_one_le_of_one_le hw hZsq)
        (mul_le_mul_of_nonneg_right hpow hd)
      _ = w*(Z^2+d) := by ring
      _ ≤ _ := by
        simpa only [mul_assoc] using le_mul_of_one_le_left
          (mul_nonneg (zero_le_one.trans hw) (by positivity : 0 ≤ Z^2+d)) join_constant_one_le
  have hh := source_sqrt_pair_le
    (U := 1+4*Real.pi*R/N) (V := 1+(N*n/(X/Z))^ε*G/(N*(X/Z)))
    hS (by positivity) (by positivity)
    (zero_le_one.trans join_constant_one_le) (by norm_num : (0 : ℝ) ≤ 1)
    (zero_le_one.trans hw) (by positivity : 0 ≤ Z^2+R/N)
    (by positivity : 0 ≤ Z^2+d) (by simpa only [mul_one] using hb.2.1) hv
  have hroot : Real.sqrt w = P^(3*ε/2) := by
    dsimp [w]
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul (zero_le_one.trans hP)]
    congr 1
    ring
  simpa only [one_mul,mul_one,hroot,d] using hh

end
end ArtinMatthews
