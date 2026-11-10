module

public import ArtinMatthews.CircleParameterChoice
public import ArtinMatthews.CircleParameterBudget
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! The source parameters in ABL Section 8.2 and the actual signed dual
frequencies in the shifted correlation. -/

noncomputable section

namespace ArtinMatthews

/-- The ABL Section 8.2 parameter, with source `X=T` and `|f|=Z=μ=1`. -/
def shiftedABLSourceParameter (M T : ℝ) (N : ℕ) : ℝ := T * M * N

/-- The literal Section 8.2 smoothness parameter, before specializing the
source shift, weight and derivative scale. -/
def ablSection82WPrime (P ε μ Z f M X : ℝ) : ℝ :=
  P^ε * (μ + Z * (1 + |f| / (M * X))) *
    (μ + Real.sqrt Z * Real.sqrt (1 + |f| / (M * X)))

/-- For the weight-one shift-one caller the fixed source seminorms permit
`Z=1` and the source variable `X` is `T`. -/
def shiftedABLSourceWPrime (ε M T : ℝ) (N : ℕ) : ℝ :=
  ablSection82WPrime (shiftedABLSourceParameter M T N) ε 1 1 1 M T

theorem shiftedABLSourceParameter_one_le {M T : ℝ} {N : ℕ}
    (hM : 1 ≤ M) (hT : 1 ≤ T) (hN : 0 < N) :
    1 ≤ shiftedABLSourceParameter M T N := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hT hM) hN'

theorem shiftedABLSourceWPrime_bounds {ε M T : ℝ} {N : ℕ}
    (hM : 1 ≤ M) (hT : 1 ≤ T) (hN : 0 < N) :
    (shiftedABLSourceParameter M T N)^ε ≤ shiftedABLSourceWPrime ε M T N ∧
      shiftedABLSourceWPrime ε M T N ≤
        3 * (1 + Real.sqrt 2) * (shiftedABLSourceParameter M T N)^ε ∧
      shiftedABLSourceWPrime ε M T N < 8 * (shiftedABLSourceParameter M T N)^ε := by
  have hP : 0 < shiftedABLSourceParameter M T N :=
    zero_lt_one.trans_le (shiftedABLSourceParameter_one_le hM hT hN)
  have hpow := Real.rpow_pos_of_pos hP ε
  have hH := one_le_mul_of_one_le_of_one_le hM hT
  have hrecip : 1 / (M*T) ≤ 1 := (div_le_one (zero_lt_one.trans_le hH)).2 hH
  have hrecip0 : 0 ≤ 1 / (M*T) := by positivity
  have h1 : 1 ≤ 1 + (1 + 1 / (M*T)) := by linarith
  have h2 : 1 ≤ 1 + Real.sqrt (1 + 1 / (M*T)) := by
    linarith [Real.sqrt_nonneg (1 + 1 / (M*T))]
  have h3 : 1 + (1 + 1 / (M*T)) ≤ 3 := by linarith
  have hsqrt : Real.sqrt (1 + 1 / (M*T)) ≤ Real.sqrt 2 :=
    Real.sqrt_le_sqrt (by linarith)
  have hsqrt2 : Real.sqrt 2 < 5 / 3 := by
    apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 5 / 3)).2
    norm_num
  simp only [shiftedABLSourceWPrime, ablSection82WPrime, abs_one, one_mul, Real.sqrt_one]
  constructor
  · calc
      _ = (shiftedABLSourceParameter M T N)^ε * 1 * 1 := by simp
      _ ≤ _ := by gcongr
  have hup : (shiftedABLSourceParameter M T N)^ε * (1 + (1 + 1 / (M*T))) *
        (1 + Real.sqrt (1 + 1 / (M*T))) ≤
      3 * (1 + Real.sqrt 2) * (shiftedABLSourceParameter M T N)^ε := by
    calc
      _ ≤ (shiftedABLSourceParameter M T N)^ε * 3 * (1 + Real.sqrt 2) := by
        gcongr <;> linarith
      _ = _ := by ring
  exact ⟨hup, hup.trans_lt (mul_lt_mul_of_pos_right (by linarith) hpow)⟩

/-- The source detector uses `3 * ceil(P^A)`, including at the smallest
admissible source scale. -/
theorem shiftedABLSource_circleQ_bounds {P A : ℝ} (hP : 1 ≤ P) (hA : 0 ≤ A) :
    1 ≤ circlePowerQ P A ∧ circlePowerQ P A ≤ 6 * P^A := by
  have hpow : 1 ≤ P^A := Real.one_le_rpow hP hA
  refine ⟨hpow.trans circlePowerQ_lower, ?_⟩
  have hceil := Nat.ceil_lt_add_one (zero_le_one.trans hpow)
  change 3 * (⌈P^A⌉₊ : ℝ) ≤ _
  linarith

/-- The fixed nonzero Kloosterman argument in (5.9). -/
def shiftedABLFirstIndex (m3 m4 : ℕ) : ℕ := ((m3 : ℤ) - m4).natAbs

/-- The signed dual frequency in the actual convolution (5.6). -/
def shiftedABLDualFrequency (m3 m4 k1 k2 : ℕ) : ℤ :=
  (m4 : ℤ) * k2 - (m3 : ℤ) * k1

theorem shiftedABLSource_cofactor_bounds {M : ℝ} {d m3 m4 : ℕ}
    (hM : 1 ≤ M) (hd : 0 < d) (hne : m3 ≠ m4)
    (hm1 : M ≤ ((d*m3 : ℕ) : ℝ)) (hm1' : ((d*m3 : ℕ) : ℝ) ≤ 2*M)
    (hm2 : M ≤ ((d*m4 : ℕ) : ℝ)) (hm2' : ((d*m4 : ℕ) : ℝ) ≤ 2*M) :
    let B := M / (d : ℝ)
    (B ≤ m3 ∧ (m3 : ℝ) ≤ 2*B) ∧ (B ≤ m4 ∧ (m4 : ℝ) ≤ 2*B) ∧
      (1 ≤ shiftedABLFirstIndex m3 m4 ∧ (shiftedABLFirstIndex m3 m4 : ℝ) ≤ 2*B) ∧
      (B^2 ≤ ((m3*m4 : ℕ) : ℝ) ∧ ((m3*m4 : ℕ) : ℝ) ≤ 4*B^2) := by
  dsimp
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hB0 : 0 < M / (d : ℝ) := by positivity
  simp only [Nat.cast_mul] at hm1 hm1' hm2 hm2' ⊢
  have hlow3 : M/(d : ℝ) ≤ m3 := (div_le_iff₀ hd0).2 (by linarith only [hm1])
  have hlow4 : M/(d : ℝ) ≤ m4 := (div_le_iff₀ hd0).2 (by linarith only [hm2])
  have hhigh3 : (m3 : ℝ) ≤ 2*(M/(d : ℝ)) := by
    rw [← mul_div_assoc]
    exact (le_div_iff₀ hd0).2 (by linarith only [hm1'])
  have hhigh4 : (m4 : ℝ) ≤ 2*(M/(d : ℝ)) := by
    rw [← mul_div_assoc]
    exact (le_div_iff₀ hd0).2 (by linarith only [hm2'])
  refine ⟨⟨hlow3, hhigh3⟩, ⟨hlow4, hhigh4⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · apply Nat.one_le_iff_ne_zero.mpr
    exact Int.natAbs_ne_zero.mpr (sub_ne_zero.mpr (by exact_mod_cast hne))
  · have hn : (shiftedABLFirstIndex m3 m4 : ℝ) = |(m3 : ℝ) - m4| := by
      simp [shiftedABLFirstIndex, Nat.cast_natAbs]
    rw [hn]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · simpa only [pow_two] using mul_le_mul hlow3 hlow4 hB0.le (Nat.cast_nonneg _)
  · calc
      _ ≤ (2*(M/(d : ℝ))) * (2*(M/(d : ℝ))) := by gcongr
      _ = _ := by ring

/-- Every nonempty signed frequency block inherits its radius bound from
a pair of dual indices in the actual dyadic windows. -/
theorem shiftedABLSource_dual_radius_le {B K1 K2 R : ℝ} {m3 m4 k1 k2 : ℕ}
    (hB : 0 ≤ B) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hm3 : (m3 : ℝ) ≤ 2*B) (hm4 : (m4 : ℝ) ≤ 2*B)
    (hk1 : (k1 : ℝ) ≤ 2*K1) (hk2 : (k2 : ℝ) ≤ 2*K2)
    (hR : R ≤ ((shiftedABLDualFrequency m3 m4 k1 k2).natAbs : ℝ)) :
    R ≤ 4*B*(K1+K2) := by
  have he : ((shiftedABLDualFrequency m3 m4 k1 k2).natAbs : ℝ) =
      |(m4 : ℝ)*k2-(m3 : ℝ)*k1| := by
    simp [shiftedABLDualFrequency, Nat.cast_natAbs]
  rw [he] at hR
  calc
    _ ≤ _ := hR
    _ ≤ (m4 : ℝ)*k2 + (m3 : ℝ)*k1 := by
      apply abs_le.mpr
      constructor <;> linarith [mul_nonneg (Nat.cast_nonneg m4 : (0 : ℝ) ≤ m4)
        (Nat.cast_nonneg k2), mul_nonneg (Nat.cast_nonneg m3 : (0 : ℝ) ≤ m3)
        (Nat.cast_nonneg k1)]
    _ ≤ (2*B)*(2*K2) + (2*B)*(2*K1) := by gcongr
    _ = _ := by ring

end ArtinMatthews
