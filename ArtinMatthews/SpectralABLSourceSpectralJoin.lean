module

public import ArtinMatthews.SpectralABLSourceMomentJoin
public import ArtinMatthews.ShiftedABLSourceBudget
public import ArtinMatthews.SpectralABLSourceConductorJoin
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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

/-! The three scalar spectral channels share the original source budget.
The growth factor L and the principal sqrt Z loss remain explicit. -/
namespace ArtinMatthews
noncomputable section

theorem spectralABL_source_total_size
    {S Z R N n G X L P ε : ℝ}
    (hS : 0 ≤ S) (hZ : 1 ≤ Z) (hR : 0 ≤ R) (hN : 0 < N) (hn : 0 ≤ n)
    (hG : 0 ≤ G) (hX : 0 < X) (hL : 1 ≤ L) (hnX : n*X ≤ L*G)
    (hP : 1 ≤ P) (hε : 0 ≤ ε)
    (hpow : (N*n/(X/Z))^ε ≤ P^(3*ε)) :
    Real.sqrt (S*(Z^2+4*Real.pi*R*Z/N))*Real.sqrt (Z^2+2*Real.pi*n*Z/N) +
      Real.sqrt (S*(1+4*Real.pi*R/N))*
        Real.sqrt (1+(N*n/(X/Z))^ε*G/(N*(X/Z))) +
      Real.sqrt (S*(1+4*Real.pi*R/N))*Real.sqrt (1+n/N) ≤
      2*spectralABLSourceJoinConstant*(1+P^(3*ε/2))*Real.sqrt (Z*L)*
        Real.sqrt S*Real.sqrt (Z^2+R/N)*Real.sqrt (Z^2+G*Z/(X*N)) := by
  let C := spectralABLSourceJoinConstant
  let M := Real.sqrt S*Real.sqrt (Z^2+R/N)*Real.sqrt (Z^2+G*Z/(X*N))
  let σ := Real.sqrt (Z*L)
  let τ := P^(3*ε/2)
  have hC : 0 ≤ C := by dsimp [C,spectralABLSourceJoinConstant]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hσ : 1 ≤ σ := Real.one_le_sqrt.mpr (one_le_mul_of_one_le_of_one_le hZ hL)
  have hτ : 0 ≤ τ := Real.rpow_nonneg (zero_le_one.trans hP) _
  have hp := spectralABL_source_principal_size hS hZ hR hN hn hG hX hL hnX
  have hc := spectralABL_source_complementary_size hS hZ hR hN hn hG hX hL hnX hP hε hpow
  have hh := spectralABL_source_holomorphic_size hS hZ hR hN hn hG hX hL hnX
  have hroot : Real.sqrt L ≤ σ := Real.sqrt_le_sqrt
    (le_mul_of_one_le_left (zero_le_one.trans hL) hZ)
  have hh' : Real.sqrt (S*(1+4*Real.pi*R/N))*Real.sqrt (1+n/N) ≤ C*σ*M := by
    calc
      _ ≤ C*Real.sqrt L*M := by simpa only [C,M,mul_assoc] using hh
      _ ≤ C*σ*M := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hroot hC) hM
  have hnum : 2*σ+τ ≤ 2*(1+τ)*σ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hσ) hτ]
  calc
    _ ≤ C*σ*M+C*τ*M+C*σ*M := add_le_add
      (add_le_add (by simpa only [C,σ,M,mul_assoc] using hp)
        (by simpa only [C,τ,M,mul_assoc] using hc)) hh'
    _ = C*M*(2*σ+τ) := by ring
    _ ≤ C*M*(2*(1+τ)*σ) := mul_le_mul_of_nonneg_left hnum (mul_nonneg hC hM)
    _ = _ := by dsimp [C,M,σ,τ]; ring

theorem ablTheorem24_source_spectral_budget
    {F n r : ℕ} {Q R Z X L S ε : ℝ}
    (hF : 0 < F) (hn : 0 < n) (hr : 0 < r)
    (hQ : (F : ℝ) ≤ Q) (hR : 1 ≤ R) (hZ : 1 ≤ Z)
    (hX : 0 < X) (hL : 1 ≤ L) (hS : 0 ≤ S) (hε : 0 ≤ ε)
    (hInv : X⁻¹ ≤ ablTheorem24SpectralParameter (Q/(F : ℝ)) R Z n r F)
    (hnX : (n : ℝ)*X ≤ L*Real.sqrt ((n : ℝ)*(Nat.gcd (r*F) n : ℝ))) :
    let N := ((r*F : ℕ) : ℝ)
    let P := ablTheorem24SpectralParameter (Q/(F : ℝ)) R Z n r F
    let G := Real.sqrt ((n : ℝ)*(Nat.gcd (r*F) n : ℝ))
    (N*n/(X/Z))^ε ≤ P^(3*ε) ∧
    Real.sqrt (S*(Z^2+4*Real.pi*R*Z/N))*Real.sqrt (Z^2+2*Real.pi*n*Z/N) +
      Real.sqrt (S*(1+4*Real.pi*R/N))*
        Real.sqrt (1+(N*n/(X/Z))^ε*G/(N*(X/Z))) +
      Real.sqrt (S*(1+4*Real.pi*R/N))*Real.sqrt (1+(n : ℝ)/N) ≤
      2*spectralABLSourceJoinConstant*(1+P^(3*ε/2))*Real.sqrt (Z*L)*
        Real.sqrt S*Real.sqrt (Z^2+R/N)*Real.sqrt (Z^2+G*Z/(X*N)) := by
  intro N P G
  have hF₀ : 0 < (F : ℝ) := Nat.cast_pos.mpr hF
  have hF₁ : 1 ≤ (F : ℝ) := by exact_mod_cast hF
  have hn₁ : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hr₁ : 1 ≤ (r : ℝ) := by exact_mod_cast hr
  have hP : P = Q*R*Z*(n : ℝ)*(r : ℝ) := by
    dsimp only [P,ablTheorem24SpectralParameter]
    field_simp [hF₀.ne'] <;> ring
  have hP₁ : 1 ≤ P := by
    rw [hP]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le
          (one_le_mul_of_one_le_of_one_le (hF₁.trans hQ) hR) hZ) hn₁) hr₁
  have hcond : (N*(n : ℝ)/(X/Z))^ε ≤ P^(3*ε) := by
    have hi : X⁻¹ ≤ Q*R*Z*(n : ℝ)*(r : ℝ) := hInv.trans_eq hP
    simpa only [N,Nat.cast_mul,hP] using
      spectralABL_source_conductor_power hF₁ hr₁ hn₁ hR hZ hQ hX hε hi
  refine ⟨hcond,?_⟩
  have hN : 0 < N := by dsimp [N]; positivity
  exact spectralABL_source_total_size hS hZ (zero_le_one.trans hR) hN
    (zero_le_one.trans hn₁) (Real.sqrt_nonneg _) hX hL hnX hP₁ hε hcond

end
end ArtinMatthews
