module

public import ArtinMatthews.GiantSignedChronologicalWord
public import ArtinMatthews.GiantSignedStateGhostGrowth


set_option backward.privateInPublic true
@[expose] public section

/-! The actual full-state exponential domain used for chronological
linearity and finite word expansion. Memory degrees remain unrestricted. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

def GiantSignedWordExponential {S B : Type*} [Fintype S] [Fintype B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {M : ℕ}
    (f : GiantSignedState PS PB M → ℂ) : Prop :=
  ∃ C u : ℝ, 0 ≤ C ∧ 0 < u ∧ ∀ s, ‖f s‖ ≤ C * u ^ (∑ g, s.2.2.1 g)

section Domain
variable {S B : Type*} [Fintype S] [Fintype B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {M : ℕ}

theorem giantSignedWordExponential_zero :
    GiantSignedWordExponential (fun _ : GiantSignedState PS PB M => (0 : ℂ)) := by
  refine ⟨0, 1, le_rfl, zero_lt_one, ?_⟩
  intro s
  simp only [norm_zero, zero_mul, le_refl]

theorem giantSignedWordExponential_add
    {f g : GiantSignedState PS PB M → ℂ}
    (hf : GiantSignedWordExponential f) (hg : GiantSignedWordExponential g) :
    GiantSignedWordExponential (fun s => f s + g s) := by
  obtain ⟨Cf, uf, hCf, huf, hf⟩ := hf
  obtain ⟨Cg, ug, hCg, hug, hg⟩ := hg
  refine ⟨Cf + Cg, uf + ug, add_nonneg hCf hCg, add_pos huf hug, ?_⟩
  intro s
  calc
    _ ≤ ‖f s‖ + ‖g s‖ := norm_add_le _ _
    _ ≤ Cf * uf ^ (∑ j, s.2.2.1 j) + Cg * ug ^ (∑ j, s.2.2.1 j) :=
      add_le_add (hf s) (hg s)
    _ ≤ Cf * (uf + ug) ^ (∑ j, s.2.2.1 j) +
        Cg * (uf + ug) ^ (∑ j, s.2.2.1 j) := add_le_add
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ huf.le (le_add_of_nonneg_right hug.le) _) hCf)
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hug.le (le_add_of_nonneg_left huf.le) _) hCg)
    _ = _ := by ring

theorem giantSignedWordExponential_sub
    {f g : GiantSignedState PS PB M → ℂ}
    (hf : GiantSignedWordExponential f) (hg : GiantSignedWordExponential g) :
    GiantSignedWordExponential (fun s => f s - g s) := by
  obtain ⟨Cf, uf, hCf, huf, hf⟩ := hf
  obtain ⟨Cg, ug, hCg, hug, hg⟩ := hg
  refine ⟨Cf + Cg, uf + ug, add_nonneg hCf hCg, add_pos huf hug, ?_⟩
  intro s
  calc
    _ ≤ ‖f s‖ + ‖g s‖ := norm_sub_le _ _
    _ ≤ Cf * uf ^ (∑ j, s.2.2.1 j) + Cg * ug ^ (∑ j, s.2.2.1 j) :=
      add_le_add (hf s) (hg s)
    _ ≤ Cf * (uf + ug) ^ (∑ j, s.2.2.1 j) +
        Cg * (uf + ug) ^ (∑ j, s.2.2.1 j) := add_le_add
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ huf.le (le_add_of_nonneg_right hug.le) _) hCf)
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hug.le (le_add_of_nonneg_left huf.le) _) hCg)
    _ = _ := by ring

theorem giantSignedWordExponential_mul (c : ℂ)
    {f : GiantSignedState PS PB M → ℂ} (hf : GiantSignedWordExponential f) :
    GiantSignedWordExponential (fun s => c * f s) := by
  obtain ⟨C, u, hC, hu, hf⟩ := hf
  refine ⟨‖c‖ * C, u, mul_nonneg (norm_nonneg _) hC, hu, ?_⟩
  intro s
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf s) (norm_nonneg _)

theorem giantSignedWordExponential_finset_sum {I : Type*} (T : Finset I)
    (f : I → GiantSignedState PS PB M → ℂ)
    (hf : ∀ i ∈ T, GiantSignedWordExponential (f i)) :
    GiantSignedWordExponential (fun s => ∑ i ∈ T, f i s) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using giantSignedWordExponential_zero
  | @insert i T hi ih =>
      have hfi := hf i (Finset.mem_insert_self _ _)
      have hT : ∀ j ∈ T, GiantSignedWordExponential (f j) :=
        fun j hj => hf j (Finset.mem_insert_of_mem hj)
      simpa only [Finset.sum_insert hi] using giantSignedWordExponential_add hfi (ih hT)

theorem giantSignedBoundary_exponential :
    GiantSignedWordExponential (@giantSignedBoundary S B _ PS PB M) := by
  refine ⟨1, 1, zero_le_one, zero_lt_one, ?_⟩
  intro s
  classical
  simp only [giantSignedBoundary, one_pow, one_mul]
  split_ifs <;> simp

end Domain

theorem giantSignedChronologicalVisit_exponential
    {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {M : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ) (q ρ : ℝ)
    {f : GiantSignedState PS PB M → ℂ} (hf : GiantSignedWordExponential f) :
    GiantSignedWordExponential (giantSignedChronologicalVisit ν V q ρ f) := by
  obtain ⟨C, u, hC, hu, hf⟩ := hf
  obtain ⟨C', u', hC', hu', hout⟩ := giantSignedStateGhostApply_exponential PS ν hν
    (fun _ => ((q / ρ ^ 2 : ℝ) : ℂ))
    (fun g => ((-(1-q) * V g / ρ : ℝ) : ℂ))
    (fun _ => ((-(1-q) / ρ : ℝ) : ℂ)) f C u hC hu
    (fun s a m => hf (s, a, m))
  refine ⟨C', u', hC', hu', ?_⟩
  rintro ⟨s, a, m⟩
  exact hout s a m

end
end ArtinMatthews
