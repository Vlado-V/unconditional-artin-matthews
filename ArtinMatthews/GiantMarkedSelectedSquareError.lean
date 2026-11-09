module

public import ArtinMatthews.GiantMarkedSelectedDamping
public import ArtinMatthews.GiantMarkedSquarePairs


set_option backward.privateInPublic true
@[expose] public section

/-! The loss from replacing the original selected-label damping by its
quotient value is supported on the actual square-divisibility rows. The
bound uses the total original weight for each predecessor. -/

noncomputable section
namespace ArtinMatthews

open scoped BigOperators

theorem giantMarkedQuotientWeight_loss {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (u : ℕ) :
    let loss := divisorWeight Finset.univ P (fun j => bandReciprocalMass (P j)) u -
      giantMarkedQuotientWeight P u
    0 ≤ loss ∧ loss ≤
      if ∃ p ∈ Finset.univ.biUnion P, p ^ 2 ∣ u then markedMajorLabelMass P else 0 := by
  classical
  let old (a : ℕ) :=
    if a ∣ u then
      (1 / 2 : ℝ) ^ (∑ j, (bandCount (P j) u - 1)) * markedMajorLabelMass P
    else 0
  let new (a : ℕ) := if a ∣ u then giantMarkedQuotientDamping P (u / a) else 0
  have hold :
      divisorWeight Finset.univ P (fun j => bandReciprocalMass (P j)) u =
        ∑ a ∈ markedMajorLabelSet P, old a := by
    apply Complex.ofReal_injective
    rw [giantMarkedWeight_label_sum P hP hdis, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro a _ha
    by_cases hd : a ∣ u
    · simp only [old, hd, ite_true, giantMarkedLabelDamping_eq_real]
    · simp only [old, hd, ite_false, Complex.ofReal_zero]
  have hm : 0 ≤ markedMajorLabelMass P := (markedMajorLabelMass_pos P hV).le
  have hterm (a : ℕ) (ha : a ∈ markedMajorLabelSet P) :
      new a ≤ old a ∧
      ((∀ p ∈ Finset.univ.biUnion P, ¬p ^ 2 ∣ u) → new a = old a) := by
    by_cases hd : a ∣ u
    · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp ha
      let h := u / markedPrimeBandProduct P t
      have hu : markedPrimeBandProduct P t * h = u := Nat.mul_div_cancel' hd
      have hle (j : J) : bandCount (P j) u - 1 ≤ bandCount (P j) h := by
        rw [← hu]
        exact giantMarkedSelectedBandCount_sub_le P hP hdis t h j
      simp only [new, old, hd, ite_true, giantMarkedQuotientDamping]
      constructor
      · apply mul_le_mul_of_nonneg_right _ hm
        have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hle j)
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hs
        rw [hk, pow_add]
        exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
      · intro hno
        have heq (j : J) : bandCount (P j) u - 1 = bandCount (P j) h := by
          rw [← hu]
          apply giantMarkedSelectedBandCount_sub_eq P hP hdis t h j
          rw [hu]
          exact hno _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, (t j).2⟩)
        rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => heq j)]
    · simp [old, new, hd]
  refine ⟨sub_nonneg.mpr ?_, ?_⟩
  · rw [hold]
    exact Finset.sum_le_sum (fun a ha => (hterm a ha).1)
  · by_cases hbad : ∃ p ∈ Finset.univ.biUnion P, p ^ 2 ∣ u
    · rw [ite_eq_left hbad]
      have hnew : 0 ≤ giantMarkedQuotientWeight P u := by
        apply Finset.sum_nonneg
        intro a _ha
        by_cases hd : a ∣ u
        · simp only [hd, ite_true, giantMarkedQuotientDamping]
          exact mul_nonneg (by positivity) hm
        · simp only [hd, ite_false, le_refl]
      exact (sub_le_self _ hnew).trans (by
        simpa only [markedMajorLabelMass, one_div] using
          divisorWeight_le Finset.univ P (fun j _ => hV j) u)
    · rw [ite_eq_right hbad, hold, giantMarkedQuotientWeight, ← Finset.sum_sub_distrib]
      apply Finset.sum_nonpos
      intro a ha
      change old a - new a ≤ 0
      rw [(hterm a ha).2 (fun p hp hsq => hbad ⟨p, hp, hsq⟩), sub_self]

theorem giantMarkedQuotientDampedSum_error {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hV : ∀ j, 0 < bandReciprocalMass (P j))
    (M N : Finset ℕ) (α β F : ℕ → ℂ) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hα : ∀ m ∈ M, ‖α m‖ ≤ C) (hβ : ∀ n ∈ N, ‖β n‖ ≤ D)
    (hFnorm : ∀ u, ‖F u‖ ≤ 1) (hF : ∀ j p, p ∈ P j → ∀ h, F (p * h) = F h) :
    ‖(∑ m ∈ M, ∑ n ∈ N, α m * β n * F (m * n - 1) *
        (divisorWeight Finset.univ P (fun j => bandReciprocalMass (P j)) (m * n - 1) : ℂ)) -
        giantMarkedQuotientDampedSum P M N α β F‖ ≤
      C * D * markedMajorLabelMass P * (giantMarkedSquareCount (Finset.univ.biUnion P) M N : ℝ) := by
  classical
  let U := Finset.univ.biUnion P
  let S := markedMajorLabelMass P
  let a (m n : ℕ) := α m * β n * F (m * n - 1) *
    ((divisorWeight Finset.univ P (fun j => bandReciprocalMass (P j)) (m * n - 1) -
      giantMarkedQuotientWeight P (m * n - 1) : ℝ) : ℂ)
  rw [giantMarkedQuotientDampedSum_eq P hP M N α β F hF, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, ← mul_sub, ← Complex.ofReal_sub]
  change ‖∑ m ∈ M, ∑ n ∈ N, a m n‖ ≤ _
  calc
    _ ≤ ∑ m ∈ M, ‖∑ n ∈ N, a m n‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ M, ∑ n ∈ N,
        if ∃ p ∈ U, p ^ 2 ∣ m * n - 1 then C * D * S else 0 := by
      apply Finset.sum_le_sum
      intro m hm
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
      let u := m * n - 1
      have hcoef : ‖α m‖ * ‖β n‖ * ‖F u‖ ≤ C * D :=
        (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          (hFnorm u)).trans (mul_le_mul (hα m hm) (hβ n hn) (norm_nonneg _) hC)
      have hloss := giantMarkedQuotientWeight_loss P hP hdis hV (m * n - 1)
      simp only [a, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hloss.1]
      calc
        _ ≤ (C * D) * (if ∃ p ∈ U, p ^ 2 ∣ u then S else 0) :=
          mul_le_mul hcoef hloss.2 hloss.1 (mul_nonneg hC hD)
        _ = _ := by
          change _ = if ∃ p ∈ U, p ^ 2 ∣ u then C * D * S else 0
          split_ifs <;> simp only [mul_zero]
    _ = _ := by
      simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      simp only [giantMarkedSquareCount, giantMarkedSquareRow, U, S, Nat.cast_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _hm
      ring

end ArtinMatthews
