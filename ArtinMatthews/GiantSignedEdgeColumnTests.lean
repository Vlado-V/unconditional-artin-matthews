module

public import ArtinMatthews.GiantSignedEdgeCoupledPairing
public import ArtinMatthews.GiantSignedEdgeTransposeBound


set_option backward.privateInPublic true
@[expose] public section

/-! Exact tests for the original weighted column and its reversed row.
Every prime law, factorial memory measure and one-sided ban is unchanged. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ}
variable [∀ j, ∀ p : P j, NeZero p.val] {t : J → ℕ}

def giantSignedEdgeColumnTest (D : ℕ) (v : ℝ)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℝ) :
    GiantSignedEdgeCoupledTest P t ℝ :=
  fun _ T _ target old out => if GiantSignedEdgePromotionBan D T target then
    v ^ (∑ j, old.1 j) * f target out else 0

def giantSignedEdgeReverseColumnTest (V : J → ℝ) (D : ℕ) (v : ℝ)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℝ) :
    GiantSignedEdgeCoupledTest P t ℝ :=
  fun S T source _ old out =>
    (∏ j, (V j) ^ (T j).card / (V j) ^ (S j).card) *
      (if GiantSignedEdgePromotionBan D S source then
        v ^ (∑ j, out.1 j) * f source old else 0)

omit [DecidableEq J] [∀ j, ∀ p : P j, NeZero p.val] in
theorem giantSignedEdgeColumnTest_nonneg (D : ℕ) {v : ℝ} (hv : 0 ≤ v)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℝ)
    (hf : ∀ target out, 0 ≤ f target out)
    (S T : (j : J) → Finset (Fin (t j))) (source target : GiantSignedPrimeTuple P t)
    (old out : GiantSignedMemory P) :
    0 ≤ giantSignedEdgeColumnTest D v f S T source target old out := by
  unfold giantSignedEdgeColumnTest
  split_ifs
  · exact mul_nonneg (pow_nonneg hv _) (hf _ _)
  · exact le_rfl

omit [DecidableEq J] [∀ j, ∀ p : P j, NeZero p.val] in
theorem giantSignedEdgeColumnTest_growth (D : ℕ) {v u B : ℝ}
    (hv : 0 ≤ v) (hu : 0 ≤ u) (hB : 0 ≤ B)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℝ)
    (hf : ∀ target out, f target out ≤ B * u ^ (∑ j, out.1 j))
    (S T : (j : J) → Finset (Fin (t j))) (source target : GiantSignedPrimeTuple P t)
    (old out : GiantSignedMemory P) :
    giantSignedEdgeColumnTest D v f S T source target old out ≤
      B * v ^ (∑ j, old.1 j) * u ^ (∑ j, out.1 j) := by
  unfold giantSignedEdgeColumnTest
  split_ifs
  · calc
      _ ≤ v ^ (∑ j, old.1 j) * (B * u ^ (∑ j, out.1 j)) :=
        mul_le_mul_of_nonneg_left (hf target out) (pow_nonneg hv _)
      _ = _ := by ring
  · exact mul_nonneg (mul_nonneg hB (pow_nonneg hv _)) (pow_nonneg hu _)

omit [DecidableEq J] [∀ j, ∀ p : P j, NeZero p.val] in
theorem giantSignedEdgeReverseColumnTest_nonneg (V : J → ℝ) (hV : ∀ j, 0 ≤ V j)
    (D : ℕ) {v : ℝ} (hv : 0 ≤ v)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℝ)
    (hf : ∀ target out, 0 ≤ f target out)
    (S T : (j : J) → Finset (Fin (t j))) (source target : GiantSignedPrimeTuple P t)
    (old out : GiantSignedMemory P) :
    0 ≤ giantSignedEdgeReverseColumnTest V D v f S T source target old out := by
  unfold giantSignedEdgeReverseColumnTest
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun j _ => div_nonneg (pow_nonneg (hV j) _)
      (pow_nonneg (hV j) _))
  · split_ifs
    · exact mul_nonneg (pow_nonneg hv _) (hf _ _)
    · exact le_rfl

omit [DecidableEq J] [∀ j, ∀ p : P j, NeZero p.val] in
theorem giantSignedEdgeReverseColumnTest_growth (V : J → ℝ) {vmin vmax v u B : ℝ}
    (hvmin : 0 < vmin) (hVmin : ∀ j, vmin ≤ V j) (hVmax : ∀ j, V j ≤ vmax)
    (D : ℕ) (hv : 0 ≤ v) (hu : 0 ≤ u) (hB : 0 ≤ B)
    (tmax : ℕ) (ht : ∀ j, t j ≤ tmax)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℝ)
    (hf : ∀ target out, f target out ≤ B * u ^ (∑ j, out.1 j))
    (S T : (j : J) → Finset (Fin (t j))) (source target : GiantSignedPrimeTuple P t)
    (old out : GiantSignedMemory P) :
    giantSignedEdgeReverseColumnTest V D v f S T source target old out ≤
      (B * (giantSignedEdgeReverseConstant vmin vmax tmax) ^ Fintype.card J) *
        u ^ (∑ j, old.1 j) * v ^ (∑ j, out.1 j) := by
  classical
  let R := (giantSignedEdgeReverseConstant vmin vmax tmax) ^ Fintype.card J
  have hR : 0 ≤ R := pow_nonneg (giantSignedEdgeReverseConstant_nonneg _ _ _) _
  have hc (A : (j : J) → Finset (Fin (t j))) (j : J) : (A j).card ≤ tmax :=
    (show (A j).card ≤ t j from by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ (A j))).trans (ht j)
  have hr := giantSignedEdgeReverseFactor_bound V hvmin hVmin hVmax
    (fun j => (S j).card) (fun j => (T j).card) tmax (hc S) (hc T)
  have hRatio : 0 ≤ ∏ j, (V j) ^ (T j).card / (V j) ^ (S j).card :=
    Finset.prod_nonneg (fun j _ => div_nonneg
      (pow_nonneg (lt_of_lt_of_le hvmin (hVmin j)).le _)
      (pow_nonneg (lt_of_lt_of_le hvmin (hVmin j)).le _))
  have htest : (if GiantSignedEdgePromotionBan D S source then
      v ^ (∑ j, out.1 j) * f source old else 0) ≤
        B * u ^ (∑ j, old.1 j) * v ^ (∑ j, out.1 j) := by
    split_ifs
    · calc
        _ ≤ v ^ (∑ j, out.1 j) * (B * u ^ (∑ j, old.1 j)) :=
          mul_le_mul_of_nonneg_left (hf source old) (pow_nonneg hv _)
        _ = _ := by ring
    · exact mul_nonneg (mul_nonneg hB (pow_nonneg hu _)) (pow_nonneg hv _)
  unfold giantSignedEdgeReverseColumnTest
  calc
    _ ≤ (∏ j, (V j) ^ (T j).card / (V j) ^ (S j).card) *
        (B * u ^ (∑ j, old.1 j) * v ^ (∑ j, out.1 j)) :=
      mul_le_mul_of_nonneg_left htest hRatio
    _ ≤ R * (B * u ^ (∑ j, old.1 j) * v ^ (∑ j, out.1 j)) :=
      mul_le_mul_of_nonneg_right hr
        (mul_nonneg (mul_nonneg hB (pow_nonneg hu _)) (pow_nonneg hv _))
    _ = _ := by dsimp [R]; ring

omit [∀ j, ∀ p : P j, NeZero p.val] in
theorem giantSignedEdgeCoupledApply_input_mul
    (ν : (j : J) → P j → ℝ) (V : J → ℝ) (ρ : ℝ) (d : ℤ)
    (a : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℝ)
    (F : GiantSignedEdgeCoupledTest P t ℝ)
    (source : GiantSignedPrimeTuple P t) (m : GiantSignedMemory P) :
    giantSignedEdgeCoupledApply ν V ρ d
        (fun S T source target old out => a source old * F S T source target old out) source m =
      a source m * giantSignedEdgeCoupledApply ν V ρ d F source m := by
  unfold giantSignedEdgeCoupledApply
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  apply Finset.sum_congr rfl
  intro T _
  apply Finset.sum_congr rfl
  intro target _
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> ring

theorem giantSignedEdgeRealStorePairing_mul
    (ν : (j : J) → P j → ℝ) (V : J → ℝ) (ρ : ℝ) (d : ℤ)
    (n : J → ℕ) (S T : (j : J) → Finset (Fin (t j))) (c : ℝ)
    (F : GiantSignedPrimeTuple P t → GiantSignedPrimeTuple P t →
      GiantSignedMemory P → GiantSignedMemory P → ℝ) :
    giantSignedEdgeRealStorePairing ν V ρ d n S T
        (fun source target old out => c * F source target old out) =
      c * giantSignedEdgeRealStorePairing ν V ρ d n S T F := by
  unfold giantSignedEdgeRealStorePairing
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro source _
  apply Finset.sum_congr rfl
  intro target _
  apply Finset.sum_congr rfl
  intro old _
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> ring

omit [∀ j, ∀ p : P j, NeZero p.val] in
theorem giantSignedEdgeReverseColumnTest_apply
    (ν : (j : J) → P j → ℝ) (V : J → ℝ) (ρ : ℝ) (d : ℤ) (D : ℕ) (v : ℝ)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℝ)
    (source : GiantSignedPrimeTuple P t) (m : GiantSignedMemory P) :
    giantSignedEdgeCoupledApply ν V ρ d (giantSignedEdgeReverseColumnTest V D v f) source m =
      f source m * giantSignedEdgeTransposePositiveApply ν V ρ d D source
        (fun _ out => v ^ (∑ j, out.1 j)) m := by
  unfold giantSignedEdgeCoupledApply giantSignedEdgeReverseColumnTest
    giantSignedEdgeTransposePositiveApply giantSignedEdgePositiveFixedApply
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  apply Finset.sum_congr rfl
  intro T _
  by_cases hb : GiantSignedEdgePromotionBan D S source
  · simp only [hb, ite_true, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro target _
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> ring
  · simp only [hb, ite_false, mul_zero, ite_self, Finset.sum_const_zero]

theorem giantSignedEdgeColumnTest_block_reverse
    (ν : (j : J) → P j → ℝ) (V : J → ℝ) (hV : ∀ j, V j ≠ 0)
    (ρ : ℝ) (d : ℤ) (D : ℕ) (v : ℝ)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℝ)
    (hf : ∀ target m σ, f target (giantSignedMemoryPermute m σ) = f target m)
    (n : J → ℕ) (S T : (j : J) → Finset (Fin (t j))) :
    giantSignedEdgeRealStorePairing ν V ρ d n S T (giantSignedEdgeColumnTest D v f S T) =
      giantSignedEdgeRealStorePairing ν V ρ (-d) n T S
        (giantSignedEdgeReverseColumnTest V D v f T S) := by
  have hr := giantSignedEdgeRealStorePairing_ban_reverse ν V hV ρ d D n S T
    (fun _ target old out => v ^ (∑ j, old.1 j) * f target out)
    (fun _ _ _ _ _ => rfl)
    (fun _ target old out σ =>
      congrArg (fun z => v ^ (∑ j, old.1 j) * z) (hf target out σ))
  rw [← giantSignedEdgeRealStorePairing_mul] at hr
  exact hr

end
end ArtinMatthews
