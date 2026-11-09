module

public import ArtinMatthews.GiantSignedMemoryState
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! The actual lifespan baseline and its tilted fresh-prime law. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

def giantSignedVisitLoss {n : ℕ} (q : Fin n → ℝ) : ℝ := ∑ i, (1 - q i)

def giantSignedPrimeBaseline {n : ℕ} (q : Fin n → ℝ) (p : ℕ) : ℝ :=
  1 - giantSignedVisitLoss q / p

def giantSignedPrimeDensity {n : ℕ} (q : Fin n → ℝ) (p : ℕ) : ℝ :=
  (giantSignedPrimeBaseline q p)⁻¹

def giantSignedTiltedPrimeLaw (P : Finset ℕ) {n : ℕ} (q : Fin n → ℝ) (p : P) : ℝ :=
  markedHarmonicAtom P p / giantSignedPrimeBaseline q p.val

theorem giantSignedTiltedPrimeLaw_eq (P : Finset ℕ) {n : ℕ} (q : Fin n → ℝ) (p : P) :
    giantSignedTiltedPrimeLaw P q p = markedHarmonicAtom P p * giantSignedPrimeDensity q p.val := rfl

theorem giantSignedVisitLoss_nonneg {n : ℕ} (q : Fin n → ℝ) (hq : ∀ i, q i ≤ 1) :
    0 ≤ giantSignedVisitLoss q :=
  Finset.sum_nonneg fun i _ => sub_nonneg.mpr (hq i)

theorem giantSignedVisitLoss_le {n : ℕ} (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i) :
    giantSignedVisitLoss q ≤ n := by
  calc
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => by linarith [hq i])
    _ = _ := by simp

theorem giantSignedPrimeBaseline_bounds {n p : ℕ} (q : Fin n → ℝ)
    (hp : 0 < p) (hq : ∀ i, q i ≤ 1) {δ : ℝ}
    (hδ : giantSignedVisitLoss q / p ≤ δ) (hδ1 : δ < 1) :
    0 < giantSignedPrimeBaseline q p ∧
      1 - δ ≤ giantSignedPrimeBaseline q p ∧ giantSignedPrimeBaseline q p ≤ 1 := by
  have hratio : 0 ≤ giantSignedVisitLoss q / p :=
    div_nonneg (giantSignedVisitLoss_nonneg q hq) (by exact_mod_cast hp.le)
  unfold giantSignedPrimeBaseline
  constructor
  · linarith
  constructor <;> linarith

theorem giantSignedPrimeDensity_bounds {n p : ℕ} (q : Fin n → ℝ)
    (hp : 0 < p) (hq : ∀ i, q i ≤ 1) {δ : ℝ}
    (hδ : giantSignedVisitLoss q / p ≤ δ) (hδ1 : δ < 1) :
    1 ≤ giantSignedPrimeDensity q p ∧ giantSignedPrimeDensity q p ≤ (1 - δ)⁻¹ := by
  obtain ⟨hb, hlo, hhi⟩ := giantSignedPrimeBaseline_bounds q hp hq hδ hδ1
  unfold giantSignedPrimeDensity
  constructor
  · have h : (1 : ℝ) ≤ 1 / giantSignedPrimeBaseline q p :=
      (le_div_iff₀ hb).mpr (by simpa only [one_mul] using hhi)
    simpa only [one_div, one_mul] using h
  · simpa only [one_div] using one_div_le_one_div_of_le (sub_pos.mpr hδ1) hlo

theorem giantSignedPrimeBaseline_pos_of_length {n p : ℕ} (q : Fin n → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hp : n < p) : 0 < giantSignedPrimeBaseline q p := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le n) hp)
  have hnp : (n : ℝ) < p := by exact_mod_cast hp
  have hlt : giantSignedVisitLoss q / p < 1 :=
    (div_lt_one hp0).mpr ((giantSignedVisitLoss_le q hq).trans_lt hnp)
  exact sub_pos.mpr hlt

theorem giantSignedTiltedPrimeLaw_pos (P : Finset ℕ) {n : ℕ} (q : Fin n → ℝ)
    (hV : 0 < bandReciprocalMass P) (hq : ∀ i, 0 ≤ q i)
    (hp : ∀ p : P, n < p.val) (p : P) : 0 < giantSignedTiltedPrimeLaw P q p := by
  unfold giantSignedTiltedPrimeLaw
  apply div_pos _ (giantSignedPrimeBaseline_pos_of_length q hq (hp p))
  unfold markedHarmonicAtom
  exact div_pos (one_div_pos.mpr (by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le n) (hp p)))) hV

end
end ArtinMatthews
