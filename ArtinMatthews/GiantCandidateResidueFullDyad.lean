module

public import ArtinMatthews.GiantCandidateResidueRatio
public import Mathlib.Data.ZMod.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! A full dyad retains its literal half-open endpoints and its actual
rough cardinality in the relative residue estimate. -/

namespace ArtinMatthews
noncomputable section
open Finset Filter

def giantCandidateRoughFullDyad (W : ℝ) (H : ℕ) : Finset ℕ :=
  (Ico H (2*H)).filter (fun m => ∀ p∈Nat.primesLE ⌊W⌋₊,¬p∣m)

theorem giantCandidateFullDyad_eq_Ioc {H : ℕ} (hH : 0 < H) :
    Ico H (2*H) = Ioc (H-1) (2*H-1) := by
  ext m
  simp only [mem_Ioc,mem_Ico]
  omega

theorem giantCandidateRoughResidueIoc_fullDyad {H : ℕ} (hH : 0 < H) (W : ℝ) (Q a : ℕ) :
    giantCandidateRoughResidueIoc (Nat.primesLE ⌊W⌋₊) (H-1) (2*H-1) Q a =
      (giantCandidateRoughFullDyad W H).filter (fun n => Nat.ModEq Q n a) := by
  ext n
  simp only [giantCandidateRoughResidueIoc,giantCandidateRoughFullDyad,giantCandidateFullDyad_eq_Ioc hH,
    mem_filter]
  tauto

theorem giant_candidate_rough_full_dyad_ratio_eventually (τ C A : ℝ)
    (hτ : 0 < τ) (hC : 0 ≤ C) (hA : 0 ≤ A) :
    ∀ᶠ x : ℝ in atTop,∀ H Q a : ℕ,0<Q →
      (Q:ℝ) ≤ Real.exp (C*(Real.log x)^(9/20:ℝ)) →
      (∀ p∈Nat.primesLE ⌊Real.exp ((Real.log x)^(6/25:ℝ))⌋₊,p.Coprime Q) →
      x^τ ≤ (H:ℝ) →
      let W := Real.exp ((Real.log x)^(6/25:ℝ))
      let V := markedSieveEulerProduct W
      let B := giantCandidateRoughFullDyad W H
      (H:ℝ)*V/2 ≤ (B.card:ℝ) ∧ (B.card:ℝ) ≤ 2*((H:ℝ)*V) ∧
      |(Q:ℝ)*((B.filter (fun n => Nat.ModEq Q n a)).card:ℝ)/(B.card:ℝ)-1| ≤ (Real.log x)^(-A) := by
  filter_upwards [Real.tendsto_log_atTop.eventually (giant_candidate_rough_residue_ratio_eventually
    τ C A hτ hC hA),eventually_gt_atTop (0:ℝ)] with x hratio hx
  intro H Q a hQ hQbound hcop hH
  let W := Real.exp ((Real.log x)^(6/25:ℝ))
  let P := Nat.primesLE ⌊W⌋₊
  have hH₀ : 0 < H := Nat.cast_pos.mp ((Real.rpow_pos_of_pos hx τ).trans_le hH)
  have hlen : 2*H-1-(H-1)=H := by omega
  have hlarge : Real.exp (τ*Real.log x) ≤ ((2*H-1-(H-1):ℕ):ℝ) := by
    rw [hlen,mul_comm τ,← Real.rpow_def_of_pos hx]
    exact hH
  have hB : giantCandidateRoughIoc P (H-1) (2*H-1) = giantCandidateRoughFullDyad W H := by
    unfold giantCandidateRoughIoc giantCandidateRoughFullDyad
    rw [giantCandidateFullDyad_eq_Ioc hH₀]
  dsimp only [P,W] at hB
  have h := hratio (H-1) (2*H-1) Q a hQ hQbound hcop hlarge
  simpa only [hlen,hB,giantCandidateRoughResidueIoc_fullDyad hH₀] using h

theorem giantCandidateFullDyad_residue_eq_zmod (W : ℝ) (H : ℕ) {Q : ℕ} [NeZero Q] (a : ZMod Q) :
    (giantCandidateRoughFullDyad W H).filter (fun n => Nat.ModEq Q n a.val) =
      (giantCandidateRoughFullDyad W H).filter (fun n : ℕ => (n:ZMod Q)=a) := by
  ext n
  simp only [mem_filter,← ZMod.natCast_eq_natCast_iff,ZMod.natCast_val,ZMod.cast_id]

end
end ArtinMatthews
