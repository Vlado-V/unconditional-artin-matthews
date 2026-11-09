module

public import ArtinMatthews.GiantSignedEdgeHitBounds


set_option backward.privateInPublic true
@[expose] public section

/-! Summation of the actual fresh target labels. Promoted labels are fixed
by old particles, and the original promotion ban remains in the summand. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

section Basic
variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {t : J → ℕ}

def giantSignedEdgeTargetLabelEquiv (T : (j : J) → Finset (Fin (t j))) :
    GiantSignedPrimeTuple P t ≃
      (GiantSignedPrimeTuple P (fun j => (T j).card) ×
        GiantSignedPrimeTuple P (fun j => ((T j)ᶜ).card)) where
  toFun target := (fun j => (markedRawSubsetTupleEquiv (T j) (target j)).1,
    fun j => (markedRawSubsetTupleEquiv (T j) (target j)).2)
  invFun pair j := (markedRawSubsetTupleEquiv (T j)).symm (pair.1 j, pair.2 j)
  left_inv target := by
    funext j
    exact (markedRawSubsetTupleEquiv (T j)).symm_apply_apply (target j)
  right_inv pair := by
    apply Prod.ext
    · funext j
      exact congrArg Prod.fst ((markedRawSubsetTupleEquiv (T j)).apply_symm_apply
        (pair.1 j, pair.2 j))
    · funext j
      exact congrArg Prod.snd ((markedRawSubsetTupleEquiv (T j)).apply_symm_apply
        (pair.1 j, pair.2 j))

def giantSignedFreshPrimeRealMass (ν : (j : J) → P j → ℝ)
    (T : (j : J) → Finset (Fin (t j))) (target : GiantSignedPrimeTuple P t) : ℝ :=
  ∏ j, ∏ i, ν j ((markedRawSubsetTupleEquiv (T j) (target j)).2 i)

omit [DecidableEq J] in
theorem giantSignedFreshPrimeRealMass_nonneg (ν : (j : J) → P j → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (T : (j : J) → Finset (Fin (t j)))
    (target : GiantSignedPrimeTuple P t) : 0 ≤ giantSignedFreshPrimeRealMass ν T target :=
  Finset.prod_nonneg (fun _ _ => Finset.prod_nonneg (fun _ _ => hν _ _))

omit [DecidableEq J] in
theorem giantSignedFreshPrimeMass_norm (ν : (j : J) → P j → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (T : (j : J) → Finset (Fin (t j)))
    (target : GiantSignedPrimeTuple P t) :
    ‖giantSignedFreshPrimeMass (fun j p => (ν j p : ℂ)) T target‖ =
      giantSignedFreshPrimeRealMass ν T target := by
  unfold giantSignedFreshPrimeMass giantSignedFreshPrimeRealMass
  simp only [norm_prod]
  apply Finset.prod_congr rfl
  intro j _
  apply Finset.prod_congr rfl
  intro i _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hν _ _)]

theorem giantSignedPrimeTuple_mass_sum (ν : (j : J) → P j → ℝ) (n : J → ℕ) :
    (∑ q : GiantSignedPrimeTuple P n, ∏ j, ∏ i, ν j (q j i)) =
      ∏ j, (∑ p : P j, ν j p) ^ n j := by
  calc
    _ = ∏ j, ∑ q : Fin (n j) → P j, ∏ i, ν j (q i) :=
      (Fintype.prod_sum (fun j (q : Fin (n j) → P j) => ∏ i, ν j (q i))).symm
    _ = _ := Finset.prod_congr rfl (fun j _ => (Fintype.sum_pow (ν j) (n j)).symm)

theorem giantSignedFreshPrimeMass_sum_fixed (ν : (j : J) → P j → ℝ)
    (T : (j : J) → Finset (Fin (t j)))
    (q : GiantSignedPrimeTuple P (fun j => (T j).card)) :
    (∑ target : GiantSignedPrimeTuple P t,
      if (fun j => giantSignedEdgeSelected (T j) (target j)) = q then
        giantSignedFreshPrimeRealMass ν T target else 0) =
      ∏ j, (∑ p : P j, ν j p) ^ ((T j)ᶜ).card := by
  classical
  let E := giantSignedEdgeTargetLabelEquiv (P := P) T
  have hE (pair : GiantSignedPrimeTuple P (fun j => (T j).card) ×
      GiantSignedPrimeTuple P (fun j => ((T j)ᶜ).card)) :
      (fun j => giantSignedEdgeSelected (T j) (E.symm pair j)) = pair.1 ∧
      giantSignedFreshPrimeRealMass ν T (E.symm pair) = ∏ j, ∏ i, ν j (pair.2 j i) := by
    have he := E.apply_symm_apply pair
    constructor
    · exact congrArg Prod.fst he
    · exact congrArg (fun x => ∏ j, ∏ i, ν j (x j i)) (congrArg Prod.snd he)
  rw [← Equiv.sum_comp E.symm, Fintype.sum_prod_type]
  simp_rw [(hE _).1, (hE _).2]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  exact giantSignedPrimeTuple_mass_sum ν _

omit [DecidableEq J] in
theorem giantSignedPromotionCharge_norm (V : J → ℝ) (hV : ∀ j, 0 < V j)
    (a : J → ℕ) :
    ‖giantSignedPromotionCharge V a‖ = ∏ j, (V j)⁻¹ ^ a j := by
  unfold giantSignedPromotionCharge
  simp only [norm_prod, norm_pow, norm_inv]
  apply Finset.prod_congr rfl
  intro j _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hV j)]

end Basic

section Gated
variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {t : J → ℕ}

theorem giantSignedEdgeTargetMass_eq (ν : (j : J) → P j → ℝ)
    (d : ℤ) (m : GiantSignedMemory P)
    (S T : (j : J) → Finset (Fin (t j)))
    (e : (j : J) → Fin (T j).card ↪ Fin (m.1 j)) :
    (∑ target : GiantSignedPrimeTuple P t,
      giantSignedFreshPrimeRealMass ν T target *
        (if GiantSignedEdgeHits d m target ⟨S, T, e⟩ then (1 : ℝ) else 0)) =
      (if ∀ j i, e j i ∈ giantSignedEdgeHitIndices d m j then (1 : ℝ) else 0) *
        ∏ j, (∑ p : P j, ν j p) ^ ((T j)ᶜ).card := by
  classical
  by_cases he : ∀ j i, e j i ∈ giantSignedEdgeHitIndices d m j
  · have hg (target : GiantSignedPrimeTuple P t) :
        GiantSignedEdgeHits d m target ⟨S, T, e⟩ ↔
          (fun j => giantSignedEdgeSelected (T j) (target j)) =
            giantSignedEdgePromotionPrimes m e := by
      rw [giantSignedEdgeHits_indices_labels, and_iff_right he, funext_iff]
    simp only [hg, mul_ite, mul_one, mul_zero, ite_eq_left he, one_mul]
    exact giantSignedFreshPrimeMass_sum_fixed ν T _
  · have hn (target : GiantSignedPrimeTuple P t) :
        ¬ GiantSignedEdgeHits d m target ⟨S, T, e⟩ :=
      fun hg => he ((giantSignedEdgeHits_indices_labels d m target S T e).mp hg).1
    simp only [hn, ite_false, mul_zero, Finset.sum_const_zero, ite_eq_right he, zero_mul]

theorem giantSignedEdgeTargetMass_le (ν : (j : J) → P j → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (d : ℤ) (D : ℕ) (m : GiantSignedMemory P)
    (S T : (j : J) → Finset (Fin (t j)))
    (e : (j : J) → Fin (T j).card ↪ Fin (m.1 j)) :
    (∑ target : GiantSignedPrimeTuple P t,
      giantSignedFreshPrimeRealMass ν T target *
        (if GiantSignedEdgeHits d m target ⟨S, T, e⟩ ∧
          GiantSignedEdgePromotionBan D T target then (1 : ℝ) else 0)) ≤
      (if ∀ j i, e j i ∈ giantSignedEdgeHitIndices d m j then (1 : ℝ) else 0) *
        ∏ j, (∑ p : P j, ν j p) ^ ((T j)ᶜ).card := by
  classical
  by_cases he : ∀ j i, e j i ∈ giantSignedEdgeHitIndices d m j
  · rw [ite_eq_left he, one_mul]
    calc
      _ ≤ ∑ target : GiantSignedPrimeTuple P t,
          if (fun j => giantSignedEdgeSelected (T j) (target j)) =
              giantSignedEdgePromotionPrimes m e then
            giantSignedFreshPrimeRealMass ν T target else 0 := by
        apply Finset.sum_le_sum
        intro target _
        split_ifs with hg hq hq
        · simp only [mul_one, le_refl]
        · exact False.elim (hq (funext
            ((giantSignedEdgeHits_indices_labels d m target S T e).mp hg.1).2))
        · simpa only [mul_zero] using giantSignedFreshPrimeRealMass_nonneg ν hν T target
        · simp only [mul_zero, le_refl]
      _ = _ := giantSignedFreshPrimeMass_sum_fixed ν T _
  · have hn (target : GiantSignedPrimeTuple P t) :
        ¬ (GiantSignedEdgeHits d m target ⟨S, T, e⟩ ∧
          GiantSignedEdgePromotionBan D T target) :=
      fun hg => he ((giantSignedEdgeHits_indices_labels d m target S T e).mp hg.1).1
    simp only [ite_eq_right he, hn, ite_false, mul_zero, Finset.sum_const_zero, zero_mul, le_refl]

end Gated
end
end ArtinMatthews
