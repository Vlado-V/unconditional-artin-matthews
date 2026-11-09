module

public import ArtinMatthews.CubicSieveActualArrayEuler
public import ArtinMatthews.CubicSieveJointEulerCompare


set_option backward.privateInPublic true
@[expose] public section

/-! The actual value and first derivative in (7.13). The fixed array
is kept throughout and the error uses its original truncation depth. -/

noncomputable section
namespace ArtinMatthews

open Filter Finset
open scoped BigOperators Topology

theorem cubicSieve_actualJointEuler_envelope {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, 0 < e j ∧ e j ≤ 1 / 5) (hinj : Function.Injective e)
    {α γ : ℝ} (heα : ∀ j, α ≤ e j) (hγ : 0 < γ) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      let P := fun j => markedLogPowerBand (e j) x
      let V := fun j => bandReciprocalMass (P j)
      let k := cubicSamplingTruncationDepth x
      |cubicSieveJointEulerModel P V (x ^ γ) m k 1 - independentArrayMean P V *
          cubicSieveDivisorCorrectionModel (x ^ γ) m 1| ≤
        C * (Real.log x) ^ 3 * cubicSieveSourceModelEnvelope α x ∧
      |deriv (cubicSieveJointEulerModel P V (x ^ γ) m k) 1 - independentArrayMean P V *
          deriv (cubicSieveDivisorCorrectionModel (x ^ γ) m) 1| ≤
        C * (Real.log x) ^ 3 * cubicSieveSourceModelEnvelope α x := by
  let K := 8 * (m : ℝ) + 2
  have hK : 0 < K := by dsimp only [K]; positivity
  obtain ⟨A, hA, ha⟩ := cubicSieve_actualArrayEuler_envelope e he hinj heα (mul_pos hγ hK).le
  let D := (Real.exp (Real.eulerMascheroniConstant + 1) * γ) ^ 2
  let B := D * (K * γ + 1)
  have hD : 0 < D := by dsimp only [D]; positivity
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B * A, mul_pos hB hA, ?_⟩
  have hrough := (tendsto_rpow_atTop hγ).eventually marked_rough_density_inverse_eventually
  filter_upwards [ha, hrough, Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with x harray hinverse hL₁ hx₁
  dsimp only at harray ⊢
  let P := fun j => markedLogPowerBand (e j) x
  let V := fun j => bandReciprocalMass (P j)
  let k := cubicSamplingTruncationDepth x
  let L := Real.log x
  let z := x ^ γ
  let E := cubicSieveSourceModelEnvelope α x
  have hx₀ := zero_lt_one.trans hx₁
  have hL : 0 < L := Real.log_pos hx₁
  have hz : 1 < z := Real.one_lt_rpow hx₁ hγ
  have hlogz : Real.log z = γ * L := Real.log_rpow hx₀ γ
  have hE : 0 ≤ E := by dsimp only [E, cubicSieveSourceModelEnvelope]; positivity
  have hmass : cubicSieveCorrectionAbsoluteMass z m ≤ D * L ^ 2 := by
    calc
      _ ≤ (markedSieveEulerProduct z)⁻¹ ^ 2 := cubicSieve_correctionAbsoluteMass_le z m
      _ ≤ (Real.exp (Real.eulerMascheroniConstant + 1) * Real.log z) ^ 2 :=
        pow_le_pow_left₀ (inv_nonneg.mpr (markedSieveEulerProduct_pos z).le) hinverse 2
      _ = _ := by rw [hlogz]; dsimp only [D]; ring
  have hdmass := cubicSieve_correctionDerivativeMass_le hz m
  have hdmass₀ : 0 ≤ cubicSieveCorrectionDerivativeMass z m := by
    unfold cubicSieveCorrectionDerivativeMass
    exact sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hL23 : L ^ 2 ≤ L ^ 3 := by
    rw [pow_succ]
    exact le_mul_of_one_le_right (sq_nonneg L) hL₁
  have hbudget : cubicSieveCorrectionDerivativeMass z m + cubicSieveCorrectionAbsoluteMass z m ≤ B * L ^ 3 := by
    calc
      _ ≤ K * Real.log z * (D * L ^ 2) + D * L ^ 2 :=
        add_le_add (hdmass.trans (mul_le_mul_of_nonneg_left hmass (mul_nonneg hK.le (Real.log_pos hz).le))) hmass
      _ = D * (K * γ) * L ^ 3 + D * L ^ 2 := by rw [hlogz]; ring
      _ ≤ D * (K * γ) * L ^ 3 + D * L ^ 3 :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hL23 hD.le)
      _ = _ := by dsimp only [B]; ring
  have hPr (j : J) (p : ℕ) (hp : p ∈ P j) : p.Prime := (mem_markedLogPowerBand.mp hp).1
  have hvals (S : Finset ℕ) (hS : S ∈ (Nat.primesLE ⌊z⌋₊).powerset)
      (hne : cubicSieveCorrectionCoeff z m S ≠ 0) :
      |cubicSieveFirstArrayEulerSum P V k (roughSubsetDivisor S) 1 - independentArrayMean P V| ≤ A * E ∧
      |deriv (cubicSieveFirstArrayEulerSum P V k (roughSubsetDivisor S)) 1| ≤ A * E := by
    have hlev := (cubicSieve_correctionCoeff_level hz (mem_powerset.mp hS) hne).2.2
    have heq : z ^ K = x ^ (γ * K) := (Real.rpow_mul hx₀.le γ K).symm
    exact harray (roughSubsetDivisor S) (roughSubsetDivisor_pos S
      (fun p hp => Nat.prime_of_mem_primesLE (mem_powerset.mp hS hp))) (heq ▸ hlev)
  have hv := cubicSieve_jointEuler_value_compare P V z m k (independentArrayMean P V) (A * E)
    (fun S hS hne => (hvals S hS hne).1)
  have ht := cubicSieve_jointEuler_tangent_compare P V hPr z m k (independentArrayMean P V) (A * E)
    (fun S hS hne => (hvals S hS hne).1) (fun S hS hne => (hvals S hS hne).2)
  have hvalbudget : cubicSieveCorrectionAbsoluteMass z m ≤ B * L ^ 3 :=
    (le_add_of_nonneg_left hdmass₀).trans hbudget
  refine ⟨?_, ?_⟩
  · exact hv.trans ((mul_le_mul_of_nonneg_right hvalbudget (mul_nonneg hA.le hE)).trans_eq (by ring))
  · exact ht.trans ((mul_le_mul_of_nonneg_right hbudget (mul_nonneg hA.le hE)).trans_eq (by ring))

theorem cubicSieve_actualJointEuler_log_saving {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, 0 < e j ∧ e j ≤ 1 / 5) (hinj : Function.Injective e)
    {α γ : ℝ} (hα : 0 < α) (heα : ∀ j, α ≤ e j) (hγ : 0 < γ)
    (m : ℕ) (A : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop,
      let P := fun j => markedLogPowerBand (e j) x
      let V := fun j => bandReciprocalMass (P j)
      let k := cubicSamplingTruncationDepth x
      |cubicSieveJointEulerModel P V (x ^ γ) m k 1 - independentArrayMean P V *
          cubicSieveDivisorCorrectionModel (x ^ γ) m 1| ≤ δ * (Real.log x) ^ (-A) ∧
      |deriv (cubicSieveJointEulerModel P V (x ^ γ) m k) 1 - independentArrayMean P V *
          deriv (cubicSieveDivisorCorrectionModel (x ^ γ) m) 1| ≤ δ * (Real.log x) ^ (-A) := by
  obtain ⟨C, _, hC⟩ := cubicSieve_actualJointEuler_envelope e he hinj heα hγ m
  filter_upwards [hC, cubicSieve_sourceModelEnvelope_log_saving hα C A 3 hδ,
    eventually_gt_atTop (1 : ℝ)] with x hx hsmall hx₁
  have hp : (Real.log x) ^ (3 : ℝ) = (Real.log x) ^ (3 : ℕ) := Real.rpow_natCast _ _
  rw [hp] at hsmall
  exact ⟨hx.1.trans hsmall, hx.2.trans hsmall⟩

end ArtinMatthews
