module

public import ArtinMatthews.GiantSignedTraceMemo
public import ArtinMatthews.GiantSignedTraceRows
public import ArtinMatthews.GiantSignedGhostFiniteBatch
public import ArtinMatthews.GiantSignedBirthLocalMemo


set_option backward.privateInPublic true
@[expose] public section

/-! The actual ordered ghost row pays one tilted atom for each
dependent birth assigned to this visit. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {S B : Type u} [Fintype S] [Fintype B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {M n H : ℕ}

def giantSignedGhostMemoRule (hPB : ∀ g p, p ∈ PB g → p.Prime)
    (ν : ∀ g, PB g → ℝ) (A C D : B → ℂ) (v mass Δ : ℝ)
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B M n H)) (i : Fin (n+1)) :
    GiantSignedTraceMemoRule (GiantSignedBirthMemo B M n H)
      (giantSignedGhostTraceRow (PS := PS) (M := M) ν A C D) where
  update old _ r := if hb : GiantSignedGhostBatchFits H r then
    giantSignedVisitBirthMemo hPB i (fun g => (r g).2.1) hb (fun g => (r g).2.2) old
    else old
  accept old _ r := if hb : GiantSignedGhostBatchFits H r then
    GiantSignedUniformBirthConditionalGate σ (.visit i)
      (giantSignedVisitBirthMemo hPB i (fun g => (r g).2.1) hb (fun g => (r g).2.2) old)
    else False
  cost := ENNReal.ofReal (Δ^(giantSignedUniformBirthStageNonpivots σ (.visit i)).card *
    ∏ g, Real.exp (‖C g‖ * mass * v))

theorem giantSignedGhostMemoRule_mass_le
    (hPB : ∀ g p, p ∈ PB g → p.Prime) (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (A C D : B → ℂ) {v mass Δ : ℝ} (hv : 0 < v) (hmass : 1 ≤ mass) (hΔ : 0 ≤ Δ)
    (hatom : ∀ g p, ν g p ≤ Δ) (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ mass)
    (hrow : ∀ g, ‖A g‖ + ‖D g‖ / v ≤ 1)
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B M n H)) (i : Fin (n+1))
    (old : GiantSignedBirthMemo B M n H) (s : GiantSignedState PS PB M) :
    let G := giantSignedGhostTraceRow (PS := PS) (M := M) ν A C D
    let R := giantSignedGhostMemoRule (PS := PS) hPB ν A C D v mass Δ σ i
    let W := fun x : GiantSignedState PS PB M => ENNReal.ofReal (v^(∑ g, x.2.2.1 g))
    (∑' r : G.Move s, if R.accept old s r then ENNReal.ofReal ‖G.coefficient s r‖ * W (G.target s r) else 0)
      ≤ R.cost * W s := by
  dsimp only
  let m := s.2.2
  let p := Δ^(giantSignedUniformBirthStageNonpivots σ (.visit i)).card
  let E := ∏ g, Real.exp (‖C g‖ * mass * v)
  let gate (b : B → Fin (H+1)) (born : ∀ g, Fin (b g).val → PB g) :=
    GiantSignedUniformBirthConditionalGate σ (.visit i)
      (giantSignedVisitBirthMemo hPB i (fun g => (b g).val) (fun g => Nat.le_of_lt_succ (b g).isLt) born old)
  let W (del : ∀ g, Finset (Fin (m.1 g))) (b : B → Fin (H+1)) (born : ∀ g, Fin (b g).val → PB g) : ℝ :=
    if gate b born then
      let r := giantSignedGhostFiniteBatchMove m del b born
      ‖giantSignedGhostMemoryMoveCoefficient ν A C D m r‖ *
        v^(∑ g, (giantSignedGhostMemoryMoveTarget m r).1 g)
    else 0
  let F (r : {r : GiantSignedGhostMemoryMoves m // GiantSignedGhostBatchFits H r}) : ℝ≥0∞ :=
    if GiantSignedUniformBirthConditionalGate σ (.visit i)
        (giantSignedVisitBirthMemo hPB i (fun g => (r.val g).2.1) r.property
          (fun g => (r.val g).2.2) old)
    then ENNReal.ofReal ‖giantSignedGhostMemoryMoveCoefficient ν A C D m r.val‖ *
      ENNReal.ofReal (v^(∑ g, (giantSignedGhostMemoryMoveTarget m r.val).1 g))
    else 0
  have hW (del : ∀ g, Finset (Fin (m.1 g))) (b : B → Fin (H+1)) (born : ∀ g, Fin (b g).val → PB g) :
      0 ≤ W del b born := by
    unfold W
    split_ifs
    · exact mul_nonneg (norm_nonneg _) (pow_nonneg hv.le _)
    · exact le_rfl
  have hF (del : ∀ g, Finset (Fin (m.1 g))) (b : B → Fin (H+1)) (born : ∀ g, Fin (b g).val → PB g) :
      F (giantSignedGhostFiniteBatchEquiv m H ⟨del,b,born⟩) = ENNReal.ofReal (W del b born) := by
    by_cases hg : gate b born
    · simp only [F, W, giantSignedGhostFiniteBatchEquiv, Equiv.coe_fn_mk, giantSignedGhostFiniteBatchMove]
      change (if gate b born then _ else 0) = ENNReal.ofReal (if gate b born then _ else 0)
      rw [ite_eq_left hg, ite_eq_left hg, ENNReal.ofReal_mul (norm_nonneg _)]
    · simp only [F, W, giantSignedGhostFiniteBatchEquiv, Equiv.coe_fn_mk, giantSignedGhostFiniteBatchMove]
      change (if gate b born then _ else 0) = ENNReal.ofReal (if gate b born then _ else 0)
      rw [ite_eq_right hg, ite_eq_right hg, ENNReal.ofReal_zero]
  have hreal :
      (∑ del : ∀ g, Finset (Fin (m.1 g)), ∑ b : B → Fin (H+1), ∑ born, W del b born) ≤
        p * (v^(∑ g, m.1 g) * E) :=
    giantSignedGhostConditionalRow_le ν hν A C D hv (zero_le_one.trans hmass)
      (pow_nonneg hΔ _) hrow m H gate (fun b =>
        giantSignedVisitBirthMemo_mass_le hPB ν hν hΔ hmass hatom hMass σ i
          (fun g => (b g).val) (fun g => Nat.le_of_lt_succ (b g).isLt) old)
  calc
    _ = ∑' r : GiantSignedGhostMemoryMoves m, if hb : GiantSignedGhostBatchFits H r then F ⟨r,hb⟩ else 0 := by
      apply tsum_congr
      intro r
      by_cases hr : GiantSignedGhostBatchFits H r
      · simp only [giantSignedGhostMemoRule, dite_eq_left hr, giantSignedGhostTraceRow, F, m]
      · simp only [giantSignedGhostMemoRule, dite_eq_right hr, ite_false]
    _ = ∑ del : ∀ g, Finset (Fin (m.1 g)), ∑ b : B → Fin (H+1), ∑ born,
        F (giantSignedGhostFiniteBatchEquiv m H ⟨del,b,born⟩) :=
      giantSignedGhostFiniteBatch_tsum m H F
    _ = ENNReal.ofReal (∑ del : ∀ g, Finset (Fin (m.1 g)), ∑ b : B → Fin (H+1), ∑ born, W del b born) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun del _ => Finset.sum_nonneg (fun b _ =>
        Finset.sum_nonneg (fun born _ => hW del b born)))]
      apply Finset.sum_congr rfl
      intro del _
      rw [ENNReal.ofReal_sum_of_nonneg (fun b _ => Finset.sum_nonneg (fun born _ => hW del b born))]
      apply Finset.sum_congr rfl
      intro b _
      rw [ENNReal.ofReal_sum_of_nonneg (fun born _ => hW del b born)]
      exact Finset.sum_congr rfl (fun born _ => hF del b born)
    _ ≤ ENNReal.ofReal (p * (v^(∑ g, m.1 g) * E)) := ENNReal.ofReal_le_ofReal hreal
    _ = _ := by
      change ENNReal.ofReal (p * (v^(∑ g, m.1 g) * E)) =
        ENNReal.ofReal (p * E) * ENNReal.ofReal (v^(∑ g, m.1 g))
      rw [ENNReal.ofReal_mul (pow_nonneg hΔ _), ENNReal.ofReal_mul (pow_nonneg hv.le _),
        ENNReal.ofReal_mul (pow_nonneg hΔ _)]
      ac_rfl

end
end ArtinMatthews
