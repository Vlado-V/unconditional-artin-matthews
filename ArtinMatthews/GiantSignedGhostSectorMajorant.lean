module

public import ArtinMatthews.GiantSignedGhostSimultaneous


set_option backward.privateInPublic true
@[expose] public section

/-! The degree-weighted absolute coefficient factors on each fixed
ordered ghost batch. The factorial stays on its actual batch size. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def giantSignedGhostSectorMajorant {P : Finset ℕ} (A C D : ℂ) (v : ℝ)
    (m : GiantSignedGroupMemory P) (del : Finset (Fin m.1)) (b : ℕ) : ℝ :=
  if del ⊆ giantSignedGhostZeroIndices m then
    ‖D‖^del.card * ‖A‖^((giantSignedGhostZeroIndices m).card-del.card) *
      (‖C‖^b / (Nat.factorial b : ℝ)) * v^((delᶜ).card+b)
  else 0

theorem giantSignedGhostSectorMajorant_nonneg {P : Finset ℕ} (A C D : ℂ)
    {v : ℝ} (hv : 0 ≤ v) (m : GiantSignedGroupMemory P) (del : Finset (Fin m.1)) (b : ℕ) :
    0 ≤ giantSignedGhostSectorMajorant A C D v m del b := by
  unfold giantSignedGhostSectorMajorant
  split_ifs
  · positivity
  · exact le_rfl

theorem giantSignedGhostMove_norm_degree {P : Finset ℕ} (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p)
    (A C D : ℂ) (v : ℝ) (m : GiantSignedGroupMemory P) (r : GiantSignedGhostMoves m) :
    ‖giantSignedGhostMoveCoefficient ν A C D m r‖ * v^(giantSignedGhostMoveTarget m r).1 =
      giantSignedGhostSectorMajorant A C D v m r.1 r.2.1 * ∏ i, ν (r.2.2 i) := by
  unfold giantSignedGhostMoveCoefficient giantSignedGhostSectorMajorant
  split_ifs
  · simp only [norm_mul, norm_pow, norm_div, norm_prod, Complex.norm_natCast, Complex.norm_real,
      giantSignedGhostMoveTarget, giantSignedGhostTarget]
    simp_rw [Real.norm_of_nonneg (hν _)]
    ring
  · simp only [norm_zero, zero_mul]

theorem giantSignedGhostMemoryMove_norm_degree {B : Type*} [Fintype B] {P : B → Finset ℕ}
    (ν : ∀ g, P g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (A C D : B → ℂ)
    (v : ℝ) (m : GiantSignedMemory P) (r : GiantSignedGhostMemoryMoves m) :
    ‖giantSignedGhostMemoryMoveCoefficient ν A C D m r‖ *
        v^(∑ g, (giantSignedGhostMemoryMoveTarget m r).1 g) =
      (∏ g, giantSignedGhostSectorMajorant (A g) (C g) (D g) v
        (giantSignedMemoryGroupEquiv P m g) (r g).1 (r g).2.1) *
        ∏ g, ∏ i, ν g ((r g).2.2 i) := by
  simp only [giantSignedGhostMemoryMoveCoefficient, giantSignedGhostProductMoveCoefficient,
    norm_prod, giantSignedGhostMemoryMoveTarget_degree]
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g _
  exact giantSignedGhostMove_norm_degree (ν g) (hν g) (A g) (C g) (D g) v _ (r g)

theorem giantSignedGhostSectorMajorant_sum_le {P : Finset ℕ} (A C D : ℂ)
    {v mass : ℝ} (hv : 0 < v) (hmass : 0 ≤ mass) (hrow : ‖A‖ + ‖D‖ / v ≤ 1)
    (m : GiantSignedGroupMemory P) (H : ℕ) :
    (∑ del : Finset (Fin m.1), ∑ b : Fin (H+1),
      giantSignedGhostSectorMajorant A C D v m del b.val * mass^b.val) ≤
        v^m.1 * Real.exp (‖C‖ * mass * v) := by
  classical
  let F (b : ℕ) : ℝ := (‖C‖ * mass * v)^b / (Nat.factorial b : ℝ)
  have hsum : HasSum F (Real.exp (‖C‖ * mass * v)) := by
    have h := NormedSpace.expSeries_div_hasSum_exp (‖C‖ * mass * v)
    rw [← Real.exp_eq_exp_ℝ] at h
    exact h
  have htrunc : (∑ b : Fin (H+1), F b.val) ≤ Real.exp (‖C‖ * mass * v) := by
    rw [Fin.sum_univ_eq_sum_range, ← hsum.tsum_eq]
    exact hsum.summable.sum_le_tsum _ (fun b _ => by
      dsimp [F]
      positivity)
  have hfactor (del : Finset (Fin m.1)) (hdel : del ⊆ giantSignedGhostZeroIndices m)
      (b : Fin (H+1)) :
      giantSignedGhostSectorMajorant A C D v m del b.val * mass^b.val =
        v^m.1 * ((‖D‖ / v)^del.card * ‖A‖^((giantSignedGhostZeroIndices m).card-del.card)) * F b.val := by
    have he : v^(delᶜ).card = v^m.1 / v^del.card := by
      rw [eq_div_iff (pow_ne_zero _ hv.ne'), ← pow_add]
      congr 1
      rw [Finset.card_compl, Fintype.card_fin]
      have h := Finset.card_le_card (Finset.subset_univ del)
      simp only [Finset.card_univ, Fintype.card_fin] at h
      omega
    rw [giantSignedGhostSectorMajorant, ite_eq_left hdel, pow_add, he]
    simp only [F, mul_pow, div_pow]
    ring
  have hdel :
      (Finset.univ : Finset (Finset (Fin m.1))).filter (· ⊆ giantSignedGhostZeroIndices m) =
        (giantSignedGhostZeroIndices m).powerset := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_univ, true_and]
  calc
    _ = ∑ del ∈ (giantSignedGhostZeroIndices m).powerset,
        (v^m.1 * ((‖D‖ / v)^del.card * ‖A‖^((giantSignedGhostZeroIndices m).card-del.card))) *
          ∑ b : Fin (H+1), F b.val := by
      rw [← hdel, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro del _
      by_cases hd : del ⊆ giantSignedGhostZeroIndices m
      · rw [ite_eq_left hd, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun b _ => hfactor del hd b)
      · simp only [giantSignedGhostSectorMajorant, ite_eq_right hd, zero_mul, Finset.sum_const_zero]
    _ ≤ ∑ del ∈ (giantSignedGhostZeroIndices m).powerset,
        (v^m.1 * ((‖D‖ / v)^del.card * ‖A‖^((giantSignedGhostZeroIndices m).card-del.card))) *
          Real.exp (‖C‖ * mass * v) := by
      exact Finset.sum_le_sum (fun del _ => mul_le_mul_of_nonneg_left htrunc (by positivity))
    _ = v^m.1 * Real.exp (‖C‖ * mass * v) *
        (‖D‖ / v + ‖A‖)^(giantSignedGhostZeroIndices m).card := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_pow_mul_eq_add_pow]
      ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity)
      (pow_le_one₀ (by positivity) (by simpa only [add_comm] using hrow))

end
end ArtinMatthews
