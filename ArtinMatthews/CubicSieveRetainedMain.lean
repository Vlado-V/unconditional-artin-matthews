module

public import ArtinMatthews.CubicSieveRetainedError
public import ArtinMatthews.CubicSieveJointPoleDensity


set_option backward.privateInPublic true
@[expose] public section

/-! The signed retained main term is the integral of the genuine joint
Euler value and derivative, with the literal predecessor shift. -/

noncomputable section
namespace ArtinMatthews

open Finset MeasureTheory
open scoped BigOperators ContDiff

theorem cubicSieve_retainedProgressionModel_eq_integral {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (z : ℝ) {x : ℝ} (hx : 0 < x) (m k : ℕ) :
    cubicSieveRetainedProgressionModel P V Φ z x m k =
      ∫ u in Set.Ioc x (3 * x), cubicSieveShiftedDivisorTest Φ x u *
        ((Real.log u + 2 * Real.eulerMascheroniConstant) * cubicSieveJointEulerModel P V z m k 1 +
          deriv (cubicSieveJointEulerModel P V z m k) 1) := by
  let S := (Nat.primesLE ⌊z⌋₊).powerset
  let T := representedArrayChoices P (fun _ => 1)
  let I (t : (j : J) → Fin 1 → ℕ) := markedWeightedIndices (univ.biUnion P) (representedArraySelected t) k
  let d (t : (j : J) → Fin 1 → ℕ) (i : MarkedWeightedIndex) := markedWeightedDivisor (representedArraySelected t) i
  let c (t : (j : J) → Fin 1 → ℕ) (i : MarkedWeightedIndex) := representedArrayCoefficient V (fun _ => 1) t *
    markedWeightedCoefficient (representedArrayDamping univ P (fun _ => 1) (1 / 2)) i
  let F (s : Finset ℕ) (t : (j : J) → Fin 1 → ℕ) (i : MarkedWeightedIndex) (u : ℝ) :=
    c t i * (if (d t i).Coprime (roughSubsetDivisor s) then cubicSieveShiftedDivisorTest Φ x u *
      cubicSieveShiftedDivisorLogDensity (d t i) (roughSubsetDivisor s) u else 0)
  have hInt (s : Finset ℕ) (hs : s ∈ S) (t : (j : J) → Fin 1 → ℕ) (i : MarkedWeightedIndex) :
      IntegrableOn (F s t i) (Set.Ioc x (3 * x)) := by
    have hr := roughSubsetDivisor_pos s (fun p hp => Nat.prime_of_mem_primesLE (mem_powerset.mp hs hp))
    have htest : Continuous (cubicSieveShiftedDivisorTest Φ x) :=
      hΦ.continuous.comp ((continuous_id.sub continuous_const).div_const x)
    have hden : ContinuousOn (cubicSieveShiftedDivisorLogDensity (d t i) (roughSubsetDivisor s))
        (Set.Icc x (3 * x)) :=
      (cubicSieve_shiftedDivisorLogDensity_continuousOn (d := d t i) hr.ne').mono
        (fun u hu => hx.trans_le hu.1)
    by_cases hc : (d t i).Coprime (roughSubsetDivisor s)
    · simp only [F, ite_eq_left hc]
      convert! ((htest.continuousOn.mul hden).const_mul (c t i)).integrableOn_Icc.mono_set
        Set.Ioc_subset_Icc_self using 1
      infer_instance
    · simp only [F, ite_eq_right hc, mul_zero]
      exact integrableOn_zero
  have hRow (s : Finset ℕ) (t : (j : J) → Fin 1 → ℕ) (i : MarkedWeightedIndex) :
      c t i * cubicSieveSourceProgressionModel (d t i) (roughSubsetDivisor s) Φ x =
        ∫ u in Set.Ioc x (3 * x), F s t i u := by
    by_cases hc : (d t i).Coprime (roughSubsetDivisor s)
    · simp only [cubicSieveSourceProgressionModel, F, ite_eq_left hc, integral_const_mul]
    · simp only [cubicSieveSourceProgressionModel, F, ite_eq_right hc, mul_zero, integral_zero]
  have hExpand : cubicSieveRetainedProgressionModel P V Φ z x m k =
      ∫ u in Set.Ioc x (3 * x), ∑ s ∈ S, cubicSieveCorrectionCoeff z m s *
        ∑ t ∈ T, ∑ i ∈ I t, F s t i u := by
    unfold cubicSieveRetainedProgressionModel
    change (∑ s ∈ S, cubicSieveCorrectionCoeff z m s * ∑ t ∈ T, ∑ i ∈ I t,
      c t i * cubicSieveSourceProgressionModel (d t i) (roughSubsetDivisor s) Φ x) = _
    rw [integral_finsetSum S (fun s hs => (integrable_finsetSum T (fun t _ =>
      integrable_finsetSum (I t) (fun i _ => hInt s hs t i))).const_mul _)]
    apply sum_congr rfl
    intro s hs
    rw [integral_const_mul, integral_finsetSum T (fun t _ =>
      integrable_finsetSum (I t) (fun i _ => hInt s hs t i))]
    congr 1
    apply sum_congr rfl
    intro t _
    rw [integral_finsetSum (I t) (fun i _ => hInt s hs t i)]
    exact sum_congr rfl (fun i _ => hRow s t i)
  rw [hExpand]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro u hu
  have hpos : 0 < u := hx.trans hu.1
  change (∑ s ∈ S, cubicSieveCorrectionCoeff z m s * ∑ t ∈ T, ∑ i ∈ I t, F s t i u) =
    cubicSieveShiftedDivisorTest Φ x u * ((Real.log u + 2 * Real.eulerMascheroniConstant) *
      cubicSieveJointEulerModel P V z m k 1 + deriv (cubicSieveJointEulerModel P V z m k) 1)
  rw [← cubicSieve_jointPoleDensity P V hP z m k hpos]
  simp_rw [mul_sum]
  apply sum_congr rfl
  intro s _
  apply sum_congr rfl
  intro t _
  apply sum_congr rfl
  intro i _
  dsimp only [F, c, d]
  split_ifs <;> ring

end ArtinMatthews
