module

public import ArtinMatthews.ShiftedABLRhoCommonTest
public import ArtinMatthews.ShiftedABLMellinJLogProfile
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
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

/-! The actual radial modulus profile separates into a common spatial
test and a phase in the original signed frequency. -/

noncomputable section
open Set MeasureTheory OAI
namespace ArtinMatthews

def shiftedABLRhoBlockScale (L n r : ℕ) (R : ℝ) : ℝ :=
  4*Real.pi*Real.sqrt (R*(n : ℝ))/(Real.sqrt (r : ℝ)*(3*(L : ℝ)))

def shiftedABLRhoLogShift (R m : ℝ) : ℝ := Real.log (m/R)/2

def shiftedABLRhoOrbitalArgument (F n r : ℕ) (ρ : ℤ) (c : ℝ) : ℝ :=
  shiftedABLMellinJNumerator n ρ/((F : ℝ)*Real.sqrt (r : ℝ)*c)

theorem shiftedABLRhoLogShift_bounds {R m : ℝ} (hR : 0 < R)
    (hm : R ≤ m) (hm₁ : m ≤ 2*R) :
    0 ≤ shiftedABLRhoLogShift R m ∧ shiftedABLRhoLogShift R m ≤ Real.log 2/2 := by
  have hm₀ : 0 < m := hR.trans_le hm
  unfold shiftedABLRhoLogShift
  exact ⟨div_nonneg (Real.log_nonneg ((one_le_div hR).mpr hm)) (by norm_num),
    div_le_div_of_nonneg_right (Real.log_le_log (div_pos hm₀ hR) ((div_le_iff₀ hR).mpr hm₁))
      (by norm_num)⟩

theorem shiftedABLRhoBlockScale_mul_exp_logShift {L n r : ℕ} {R : ℝ} {ρ : ℤ}
    (hR : 0 < R) (hρ : ρ ≠ 0) :
    shiftedABLRhoBlockScale L n r R*Real.exp (shiftedABLRhoLogShift R (ρ.natAbs : ℝ)) =
      shiftedABLMellinJScale L n r ρ := by
  let m := (ρ.natAbs : ℝ)
  have hm : 0 < m := Nat.cast_pos.mpr (Int.natAbs_pos.mpr hρ)
  have hExp : Real.exp (shiftedABLRhoLogShift R m) = Real.sqrt (m/R) := by
    rw [shiftedABLRhoLogShift,Real.sqrt_eq_rpow,Real.rpow_def_of_pos (div_pos hm hR)]
    congr 1
    ring
  have hSq : Real.sqrt (R*(n : ℝ))*Real.sqrt (m/R) = Real.sqrt (m*(n : ℝ)) := by
    rw [← Real.sqrt_mul (mul_nonneg hR.le (Nat.cast_nonneg n))]
    congr 1
    field_simp [hR.ne'] <;> ring
  change shiftedABLRhoBlockScale L n r R*Real.exp (shiftedABLRhoLogShift R m) = _
  rw [hExp]
  unfold shiftedABLRhoBlockScale shiftedABLMellinJScale shiftedABLMellinJNumerator
  rw [div_mul_eq_mul_div,mul_assoc (4*Real.pi),hSq]

theorem shiftedABLRhoBlockScale_pos {L n r : ℕ} {R : ℝ}
    (hL : 0 < L) (hn : 0 < n) (hr : 0 < r) (hR : 0 < R) :
    0 < shiftedABLRhoBlockScale L n r R := by
  have hL₀ : 0 < (L : ℝ) := Nat.cast_pos.mpr hL
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hr₀ : 0 < (r : ℝ) := Nat.cast_pos.mpr hr
  unfold shiftedABLRhoBlockScale
  positivity

theorem shiftedABLRhoBlockScale_log_shift {L n r : ℕ} {R x : ℝ} {ρ : ℤ}
    (hL : 0 < L) (hn : 0 < n) (hr : 0 < r) (hR : 0 < R) (hρ : ρ ≠ 0) (hx : 0 < x) :
    Real.log (x/shiftedABLMellinJScale L n r ρ) =
      Real.log (x/shiftedABLRhoBlockScale L n r R)-shiftedABLRhoLogShift R (ρ.natAbs : ℝ) := by
  have ha := shiftedABLRhoBlockScale_pos hL hn hr hR
  rw [← shiftedABLRhoBlockScale_mul_exp_logShift hR hρ]
  rw [Real.log_div hx.ne' (mul_pos ha (Real.exp_pos _)).ne',
    Real.log_mul ha.ne' (Real.exp_pos _).ne',Real.log_exp,Real.log_div hx.ne' ha.ne']
  ring

theorem shiftedABLRhoLogProfile_eq_literal (z : ℝ × ℝ) (v : ℝ) :
    markedOscillatoryFamily shiftedABLMellinJLogAmplitude shiftedABLMellinJLogPhase (z.1+z.2) v =
      shiftedABLRhoLogProfile z v := by
  unfold markedOscillatoryFamily markedOscillatoryPhase markedRealOscillator
    shiftedABLMellinJLogAmplitude shiftedABLMellinJLogPhase shiftedABLRhoLogProfile shiftedABLRhoLogBase
    shiftedABLRhoHeight FourierBridge.logPhase
  push_cast
  congr 1
  congr 1
  ring

theorem shiftedABLMellinModulusWeight_rho_separation
    {F L n r : ℕ} (hF : 0 < F) (hL : 0 < L) (hn : 0 < n) (hr : 0 < r)
    (z : ℝ × ℝ) {R c : ℝ} {ρ : ℤ} (hR : 0 < R) (hρ : ρ ≠ 0)
    (hlo : R ≤ (ρ.natAbs : ℝ)) (hhi : (ρ.natAbs : ℝ) ≤ 2*R) (hc : 0 < c) :
    let a := shiftedABLRhoBlockScale L n r R
    let x := shiftedABLRhoOrbitalArgument F n r ρ c
    shiftedABLMellinModulusWeight F L z c =
      ∫ t : ℝ, shiftedABLRhoFourierDensity t*
        FourierBridge.logPhase (t+shiftedABLRhoHeight z) (-shiftedABLRhoLogShift R (ρ.natAbs : ℝ))*
        shiftedABLRhoCommonTest a (t+shiftedABLRhoHeight z) x := by
  let x := shiftedABLRhoOrbitalArgument F n r ρ c
  let a := shiftedABLRhoBlockScale L n r R
  have hF₀ : 0 < (F : ℝ) := Nat.cast_pos.mpr hF
  have hr₀ : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hr)
  have hN := shiftedABLMellinJNumerator_pos hn hρ
  have hx : 0 < x := div_pos hN (mul_pos (mul_pos hF₀ hr₀) hc)
  have hInv : shiftedABLMellinJNumerator n ρ/((F : ℝ)*Real.sqrt (r : ℝ)*x) = c := by
    dsimp only [x,shiftedABLRhoOrbitalArgument]
    field_simp [hF₀.ne',hr₀.ne',hc.ne',hN.ne'] <;> ring
  have hRadial : shiftedABLMellinModulusWeight F L z c = shiftedABLMellinJRadial F L n r ρ z x := by
    rw [shiftedABLMellinJRadial,hInv]
  obtain ⟨hb₀,hb₁⟩ := shiftedABLRhoLogShift_bounds hR hlo hhi
  dsimp only
  rw [hRadial,shiftedABLMellinJRadial_eq_logProfile hF hL hn hr hρ,
    spectralJOscillatoryLogProfile,spectralJLogProfile,ite_eq_left hx,
    shiftedABLRhoLogProfile_eq_literal,shiftedABLRhoBlockScale_log_shift hL hn hr hR hρ hx,
    shiftedABLRhoLogProfile_split z _ _ hb₀ hb₁]
  have hx' : 0 < shiftedABLRhoOrbitalArgument F n r ρ c := hx
  simp only [shiftedABLRhoCommonTest,ite_eq_left hx',x]

end ArtinMatthews
