module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import ArtinMatthews.SpectralSeparatedSlopeCount
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Positivity.Finset


set_option backward.privateInPublic true
@[expose] public section

/-! Four signed coordinate charts give a linear packing bound for
bounded planar rows whose nonzero determinants are separated from zero. -/

noncomputable section

namespace ArtinMatthews

theorem spectral_card_le_dominant_slope {ι : Type*} (s : Finset ι) (v : ι → ℝ×ℝ)
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hv : ∀ i ∈ s, |(v i).2| ≤ |(v i).1| ∧ (v i).1 ≠ 0 ∧ |(v i).1| ≤ R)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      δ ≤ |(v i).1*(v j).2-(v i).2*(v j).1|) :
    (s.card : ℝ) ≤ 1+2*R^2/δ := by
  let f (i : ι) := (v i).2/(v i).1
  have hf (i : ι) (hi : i ∈ s) : |f i| ≤ 1 := by
    dsimp only [f]
    rw [abs_div]
    exact (div_le_one (abs_pos.mpr (hv i hi).2.1)).mpr (hv i hi).1
  have hgap (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) (hne : i ≠ j) :
      δ/R^2 ≤ |f i-f j| := by
    have hdet : (v i).1*(v j).2-(v i).2*(v j).1 =
        ((v i).1*(v j).1)*(f j-f i) := by
      dsimp only [f]
      field_simp [(hv i hi).2.1,(hv j hj).2.1]
    apply (div_le_iff₀ (sq_pos_of_pos hR)).mpr
    calc
      δ ≤ |(v i).1*(v j).2-(v i).2*(v j).1| := hd i hi j hj hne
      _ = (|(v i).1| * |(v j).1|)*|f i-f j| := by rw [hdet,abs_mul,abs_mul,abs_sub_comm (f j)]
      _ ≤ R^2 * |f i-f j| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        rw [sq]
        exact mul_le_mul (hv i hi).2.2 (hv j hj).2.2 (abs_nonneg _) hR.le
      _ = _ := mul_comm _ _
  simpa only [div_div_eq_mul_div] using
    spectral_card_le_separated_slopes s f (show 0 < δ/R^2 by positivity) hf hgap

theorem spectral_card_le_dominant_rows {ι : Type*} (s : Finset ι) (v : ι → ℝ×ℝ)
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hv : ∀ i ∈ s, |(v i).2| ≤ |(v i).1| ∧ (v i).1 ≠ 0 ∧ |(v i).1| ≤ R)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (v i).1 = -(v j).1 ∨ δ ≤ |(v i).1*(v j).2-(v i).2*(v j).1|) :
    (s.card : ℝ) ≤ 2*(1+2*R^2/δ) := by
  classical
  let p (i : ι) := 0 < (v i).1
  let sp := s.filter p
  let sn := s.filter (fun i => ¬p i)
  have hvp (i : ι) (hi : i ∈ sp) := hv i (Finset.mem_filter.mp hi).1
  have hvn (i : ι) (hi : i ∈ sn) := hv i (Finset.mem_filter.mp hi).1
  have hp (i : ι) (hi : i ∈ sp) (j : ι) (hj : j ∈ sp) (hne : i ≠ j) :
      δ ≤ |(v i).1*(v j).2-(v i).2*(v j).1| := by
    obtain ⟨his,hi'⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjs,hj'⟩ := Finset.mem_filter.mp hj
    rcases hd i his j hjs hne with ha | h
    · change 0 < (v i).1 at hi'
      change 0 < (v j).1 at hj'
      linarith
    · exact h
  have hn (i : ι) (hi : i ∈ sn) (j : ι) (hj : j ∈ sn) (hne : i ≠ j) :
      δ ≤ |(v i).1*(v j).2-(v i).2*(v j).1| := by
    obtain ⟨his,hi'⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjs,hj'⟩ := Finset.mem_filter.mp hj
    rcases hd i his j hjs hne with ha | h
    · have hni : (v i).1 < 0 := lt_of_le_of_ne (le_of_not_gt hi') (hvn i hi).2.1
      have hnj : (v j).1 < 0 := lt_of_le_of_ne (le_of_not_gt hj') (hvn j hj).2.1
      linarith
    · exact h
  have hcp := spectral_card_le_dominant_slope sp v hR hδ hvp hp
  have hcn := spectral_card_le_dominant_slope sn v hR hδ hvn hn
  have hc : (sp.card : ℝ)+(sn.card : ℝ) = (s.card : ℝ) := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := s) p
  linarith only [hc,hcp,hcn]

theorem spectral_card_le_planar_rows {ι : Type*} (s : Finset ι) (v : ι → ℝ×ℝ)
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hv : ∀ i ∈ s, v i ≠ (0,0) ∧ |(v i).1| ≤ R ∧ |(v i).2| ≤ R)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ((v i).1 = -(v j).1 ∧ (v i).2 = -(v j).2) ∨
        δ ≤ |(v i).1*(v j).2-(v i).2*(v j).1|) :
    (s.card : ℝ) ≤ 4*(1+2*R^2/δ) := by
  classical
  let p (i : ι) := |(v i).2| ≤ |(v i).1|
  let s₁ := s.filter p
  let s₂ := s.filter (fun i => ¬p i)
  let w (i : ι) := ((v i).2,(v i).1)
  have h₁ := spectral_card_le_dominant_rows s₁ v hR hδ
    (by
      intro i hi
      obtain ⟨his,hi'⟩ := Finset.mem_filter.mp hi
      refine ⟨hi',?_,(hv i his).2.1⟩
      intro hx
      have hy : (v i).2 = 0 := by
        apply abs_eq_zero.mp
        apply le_antisymm _ (abs_nonneg _)
        change |(v i).2| ≤ |(v i).1| at hi'
        simpa only [hx,abs_zero] using hi'
      exact (hv i his).1 (Prod.ext hx hy))
    (by
      intro i hi j hj hne
      exact (hd i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hne).imp And.left id)
  have h₂ := spectral_card_le_dominant_rows s₂ w hR hδ
    (by
      intro i hi
      obtain ⟨his,hi'⟩ := Finset.mem_filter.mp hi
      have hlt : |(v i).1| < |(v i).2| := lt_of_not_ge hi'
      exact ⟨hlt.le,abs_pos.mp ((abs_nonneg _).trans_lt hlt),(hv i his).2.2⟩)
    (by
      intro i hi j hj hne
      refine (hd i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hne).imp And.right ?_
      intro h
      dsimp only [w]
      rwa [show (v i).2*(v j).1-(v i).1*(v j).2 = -((v i).1*(v j).2-(v i).2*(v j).1) by ring,
        abs_neg])
  have hc : (s₁.card : ℝ)+(s₂.card : ℝ) = (s.card : ℝ) := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := s) p
  linarith only [hc,h₁,h₂]

end ArtinMatthews
