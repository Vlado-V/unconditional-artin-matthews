module

public import ArtinMatthews.CubicSamplingBaselineCRT
public import ArtinMatthews.CubicSamplingSourceTruncation


set_option backward.privateInPublic true
@[expose] public section

/-! The retained Section 6.3 array contributes through its exact signed
indexed divisor polynomial, with the norm-class modulus d*r. -/

noncomputable section
namespace ArtinMatthews

open Filter OAI OAI.SevenEighths
open scoped BigOperators ContDiff

theorem giantCubicSampling_baselineTruncation_eq {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (a : J → ℕ) (k : ℕ)
    (η : HeckeFamily.Character) {M : ℕ} (χ : DirichletCharacter ℂ M)
    (Φ : ℝ → ℝ) (x : ℝ) (r : ℕ) :
    giantCubicSamplingBaselineSum η χ
      (fun u => (cubicSamplingArrayTruncation P V a k u : ℂ)) Φ x r =
      ∑ t ∈ representedArrayChoices P a,
        ∑ i ∈ markedWeightedIndices (Finset.univ.biUnion P) (representedArraySelected t) k,
          ((representedArrayCoefficient V a t *
            markedWeightedCoefficient (representedArrayDamping Finset.univ P a (1 / 2)) i : ℝ) : ℂ) *
          giantCubicSamplingDivisorBaseline η χ Φ x (markedWeightedDivisor (representedArraySelected t) i) r := by
  unfold giantCubicSamplingBaselineSum
  simp_rw [cubicSampling_arrayTruncation_eq_divisors, Complex.ofReal_sum, apply_ite,
    Complex.ofReal_zero, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [giantCubicSamplingDivisorBaseline, giantCubicSamplingBaselineSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _hu
  split_ifs <;> simp

theorem giantCubicSampling_actualArray_retained_bound
    {J : Type*} [Fintype J] (e : J → ℝ) (he : ∀ j, 0 < e j ∧ e j ≤ 1 / 5)
    (hinj : Function.Injective e) (a : J → ℕ) (ha : ∀ j, 0 < a j)
    (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hs : Function.support Φ ⊆ Set.Ioo 1 2)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      let P := fun j => markedLogPowerBand (e j) x
      let V := fun j => bandReciprocalMass (P j)
      let k := cubicSamplingTruncationDepth x
      let η := cubicNumeratorHeckeCharacter A hA
      ∀ R : ℕ, (∑ r ∈ Finset.Icc 1 R,
        ‖giantCubicSamplingBaselineSum η χ
          (fun u => (cubicSamplingArrayTruncation P V a k u : ℂ)) Φ x r‖) ≤
        C * ((R : ℝ) * x ^ γ) *
          (((R : ℝ) * x ^ γ) * Real.sqrt x + ((R : ℝ) * x ^ γ) ^ 2) := by
  obtain ⟨C, hC, hclass⟩ := giantCubicSamplingDivisorBaseline_norm_le A hA hnoncube χ Φ hΦ hs
  refine ⟨C, hC, ?_⟩
  filter_upwards [cubicSampling_actualArray_retained_eventually e he hinj a ha hγ,
    eventually_ge_atTop (1 : ℝ)] with x hxRet hx
  dsimp only
  obtain ⟨_herr, hlevel, hmass⟩ := hxRet
  let P := fun j => markedLogPowerBand (e j) x
  let V := fun j => bandReciprocalMass (P j)
  let k := cubicSamplingTruncationDepth x
  let η := cubicNumeratorHeckeCharacter A hA
  let D := x ^ γ
  have hD : 0 ≤ D := Real.rpow_nonneg (zero_le_one.trans hx) _
  let I := representedArrayChoices P a
  let K (t : (j : J) → Fin (a j) → ℕ) :=
    markedWeightedIndices (Finset.univ.biUnion P) (representedArraySelected t) k
  let d (t : (j : J) → Fin (a j) → ℕ) (i : MarkedWeightedIndex) :=
    markedWeightedDivisor (representedArraySelected t) i
  let c (t : (j : J) → Fin (a j) → ℕ) (i : MarkedWeightedIndex) :=
    representedArrayCoefficient V a t *
      markedWeightedCoefficient (representedArrayDamping Finset.univ P a (1 / 2)) i
  intro R
  let G := ((R : ℝ) * D) * Real.sqrt x + ((R : ℝ) * D) ^ 2
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hper (r : ℕ) (hr : r ∈ Finset.Icc 1 R) :
      ‖giantCubicSamplingBaselineSum η χ
        (fun u => (cubicSamplingArrayTruncation P V a k u : ℂ)) Φ x r‖ ≤ D * (C * G) := by
    rw [giantCubicSampling_baselineTruncation_eq P V a k η χ Φ x r]
    change ‖∑ t ∈ I, ∑ i ∈ K t, (c t i : ℂ) *
      giantCubicSamplingDivisorBaseline η χ Φ x (d t i) r‖ ≤ _
    have hrow (t : (j : J) → Fin (a j) → ℕ) (ht : t ∈ I)
        (i : MarkedWeightedIndex) (hi : i ∈ K t) :
        ‖giantCubicSamplingDivisorBaseline η χ Φ x (d t i) r‖ ≤ C * G := by
      obtain ⟨hd, _hsq, hdx⟩ := hlevel t ht i hi
      obtain ⟨hrpos, hrR⟩ := Finset.mem_Icc.mp hr
      have hprod : (((d t i) * r : ℕ) : ℝ) ≤ (R : ℝ) * D := by
        rw [Nat.cast_mul, mul_comm (R : ℝ) D]
        exact mul_le_mul hdx (Nat.cast_le.mpr hrR) (Nat.cast_nonneg _) hD
      exact (hclass x hx (d t i) r hd hrpos).trans
        (mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_right hprod (Real.sqrt_nonneg _))
            (pow_le_pow_left₀ (Nat.cast_nonneg _) hprod 2)) hC.le)
    calc
      _ ≤ ∑ t ∈ I, ∑ i ∈ K t, ‖(c t i : ℂ) *
          giantCubicSamplingDivisorBaseline η χ Φ x (d t i) r‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
      _ ≤ ∑ t ∈ I, ∑ i ∈ K t, |c t i| * (C * G) := by
        apply Finset.sum_le_sum
        intro t ht
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hrow t ht i hi) (abs_nonneg _)
      _ = (∑ t ∈ I, ∑ i ∈ K t, |c t i|) * (C * G) := by simp_rw [← Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hmass (mul_nonneg hC.le hG)
  calc
    _ ≤ ∑ _r ∈ Finset.Icc 1 R, D * (C * G) := Finset.sum_le_sum hper
    _ = (R : ℝ) * (D * (C * G)) := by simp
    _ = _ := by dsimp only [G, D]; ring

end ArtinMatthews
