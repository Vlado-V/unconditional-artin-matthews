module

public import ArtinMatthews.MarkedMajorOscillatoryDerivativesBase
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
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


set_option backward.privateInPublic true
@[expose] public section

/-! Actual arbitrary-order polynomial bounds for compact smooth oscillatory families. -/

namespace ArtinMatthews
noncomputable section
open Set
open scoped ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def markedOscillatoryPhase (B : E → ℝ) (θ : ℝ) (x : E) : ℂ :=
  markedRealOscillator (θ * B x)

def markedOscillatoryFamily (A : E → ℂ) (B : E → ℝ) (θ : ℝ) (x : E) : ℂ :=
  A x * markedOscillatoryPhase B θ x

theorem markedOscillatoryPhase_contDiff (B : E → ℝ) (hB : ContDiff ℝ ∞ B) (θ : ℝ) :
    ContDiff ℝ ∞ (markedOscillatoryPhase B θ) :=
  markedRealOscillator_contDiff.comp (contDiff_const.mul hB)

theorem markedOscillatoryFamily_contDiff (A : E → ℂ) (B : E → ℝ)
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (θ : ℝ) :
    ContDiff ℝ ∞ (markedOscillatoryFamily A B θ) :=
  hA.mul (markedOscillatoryPhase_contDiff B hB θ)

/-- The constants are chosen before the real oscillation parameter.  Every
derivative order up to n has its precise corresponding polynomial degree. -/
theorem markedOscillatoryPhase_compact_derivative_bound
    (B : E → ℝ) (hB : ContDiff ℝ ∞ B) (K : Set E) (hK : IsCompact K) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i ≤ n, ∀ θ : ℝ, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ i (markedOscillatoryPhase B θ) x‖ ≤ C * (1 + |θ|) ^ i := by
  obtain ⟨M, hM, hbound⟩ := compact_norm_iteratedFDeriv_bound B hB K hK n
  refine ⟨(n.factorial : ℝ) * (M + 1) ^ n, by positivity, fun i hi θ x hx => ?_⟩
  let D : ℝ := (M + 1) * (1 + |θ|)
  have hD : 1 ≤ D := one_le_mul_of_one_le_of_one_le
    (by linarith) (by linarith [abs_nonneg θ])
  have hinner : ∀ j, 1 ≤ j → j ≤ i →
      ‖iteratedFDeriv ℝ j (fun y => θ * B y) x‖ ≤ D ^ j := by
    intro j hj hji
    have he : iteratedFDeriv ℝ j (fun y => θ * B y) x =
        θ • iteratedFDeriv ℝ j B x :=
      by
        simpa only [smul_eq_mul] using iteratedFDeriv_const_smul_apply'
          (a := θ) (i := j) (x := x) (hB.of_le (by simp)).contDiffAt
    rw [he, norm_smul, Real.norm_eq_abs]
    calc
      |θ| * ‖iteratedFDeriv ℝ j B x‖ ≤ |θ| * M :=
        mul_le_mul_of_nonneg_left (hbound j (hji.trans hi) x hx) (abs_nonneg θ)
      _ ≤ D := by dsimp [D]; nlinarith [abs_nonneg θ]
      _ ≤ D ^ j := le_self_pow₀ hD (by omega)
  have hc := norm_iteratedFDeriv_comp_le (𝕜 := ℝ)
    markedRealOscillator_contDiff (contDiff_const.mul hB) (n := i) (by simp) x
    (C := 1) (D := D) (fun j _ => (markedRealOscillator_norm_iteratedFDeriv j _).le) hinner
  change ‖iteratedFDeriv ℝ i (markedOscillatoryPhase B θ) x‖ ≤ _ at hc
  calc
    ‖iteratedFDeriv ℝ i (markedOscillatoryPhase B θ) x‖ ≤
        (i.factorial : ℝ) * 1 * D ^ i := hc
    _ = ((i.factorial : ℝ) * (M + 1) ^ i) * (1 + |θ|) ^ i := by
      dsimp [D]
      rw [mul_pow]
      ring
    _ ≤ ((n.factorial : ℝ) * (M + 1) ^ n) * (1 + |θ|) ^ i := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul (by exact_mod_cast Nat.factorial_le hi)
        (pow_le_pow_right₀ (by linarith : 1 ≤ M + 1) hi) (by positivity) (by positivity)

/-- A smooth amplitude times the actual unit-modulus phase has arbitrary-order
polynomial derivative growth, uniformly on the given compact set. -/
theorem markedOscillatoryFamily_compact_derivative_bound
    (A : E → ℂ) (B : E → ℝ) (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    (K : Set E) (hK : IsCompact K) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ n (markedOscillatoryFamily A B θ) x‖ ≤ C * (1 + |θ|) ^ n := by
  obtain ⟨MA, hMA, hA_bound⟩ := compact_norm_iteratedFDeriv_bound A hA K hK n
  obtain ⟨CB, hCB, hB_bound⟩ := markedOscillatoryPhase_compact_derivative_bound B hB K hK n
  let C : ℝ := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * MA * CB
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => by positivity)
  refine ⟨C + 1, by linarith, fun θ x hx => ?_⟩
  have hθ : 1 ≤ 1 + |θ| := by linarith [abs_nonneg θ]
  calc
    ‖iteratedFDeriv ℝ n (markedOscillatoryFamily A B θ) x‖ ≤
        ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i A x‖ *
          ‖iteratedFDeriv ℝ (n - i) (markedOscillatoryPhase B θ) x‖ :=
      norm_iteratedFDeriv_mul_le hA (markedOscillatoryPhase_contDiff B hB θ) x (by simp)
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * MA * CB * (1 + |θ|) ^ n := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
      have hBi := hB_bound (n - i) (Nat.sub_le n i) θ x hx
      have hpow := pow_le_pow_right₀ hθ (Nat.sub_le n i)
      calc
        _ ≤ (n.choose i : ℝ) * MA * (CB * (1 + |θ|) ^ (n - i)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hA_bound i hi' x hx) (by positivity))
            hBi (norm_nonneg _) (by positivity)
        _ ≤ (n.choose i : ℝ) * MA * (CB * (1 + |θ|) ^ n) := by gcongr
        _ = _ := by ring
    _ = C * (1 + |θ|) ^ n := by rw [Finset.sum_mul]
    _ ≤ (C + 1) * (1 + |θ|) ^ n := by gcongr; linarith

/-- Evaluation on any n unit directions gives the same sharp degree n. -/
theorem markedOscillatoryFamily_compact_directional_bound
    (A : E → ℂ) (B : E → ℝ) (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    (K : Set E) (hK : IsCompact K) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ, ∀ x ∈ K, ∀ v : Fin n → E,
      (∀ j, ‖v j‖ ≤ 1) →
      ‖iteratedFDeriv ℝ n (markedOscillatoryFamily A B θ) x v‖ ≤ C * (1 + |θ|) ^ n := by
  obtain ⟨C, hC, hb⟩ := markedOscillatoryFamily_compact_derivative_bound A B hA hB K hK n
  refine ⟨C, hC, fun θ x hx v hv => ?_⟩
  have hvnorm : ‖v‖ ≤ 1 := (pi_norm_le_iff_of_nonneg (by norm_num)).mpr hv
  exact ((iteratedFDeriv ℝ n (markedOscillatoryFamily A B θ) x).unit_le_opNorm hvnorm).trans
    (hb θ x hx)

end
end ArtinMatthews
