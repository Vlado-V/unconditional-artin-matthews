module

public import ArtinMatthews.SourceComparisonMarkWeight
public import ArtinMatthews.GiantCandidateFirstEndpoint


set_option backward.privateInPublic true
@[expose] public section

/-! The combined divisor model uses the literal inert array and the actual
active reciprocal list normalizations. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

variable {G H : Type*} [Fintype G] [Fintype H]

private def comparisonChoicesSumEquiv (t : G → ℕ) (u : H → ℕ) :
    ((g : G ⊕ H) → Fin (Sum.elim t u g) → ℕ) ≃
      (((g : G) → Fin (t g) → ℕ) × ((g : H) → Fin (u g) → ℕ)) :=
  Equiv.sumPiEquivProdPi (fun g : G ⊕ H => Fin (Sum.elim t u g) → ℕ)

private theorem comparisonChoices_sum_map (P : G → Finset ℕ) (Q : H → Finset ℕ)
    (t : G → ℕ) (u : H → ℕ) :
    (sourceComparisonMarkChoices (Sum.elim P Q) (Sum.elim t u)).map
      (comparisonChoicesSumEquiv t u).toEmbedding =
      sourceComparisonMarkChoices P t ×ˢ sourceComparisonMarkChoices Q u := by
  classical
  let E := comparisonChoicesSumEquiv t u
  change (sourceComparisonMarkChoices (Sum.elim P Q) (Sum.elim t u)).map E.toEmbedding = _
  ext z
  rw [mem_map, mem_product]
  constructor
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨hm, hi⟩ := (mem_sourceComparisonMarkChoices (Sum.elim P Q) (Sum.elim t u) l).mp hl
    exact ⟨(mem_sourceComparisonMarkChoices P t _).mpr
      ⟨fun g i => hm (.inl g) i, fun g => hi (.inl g)⟩,
      (mem_sourceComparisonMarkChoices Q u _).mpr
        ⟨fun g i => hm (.inr g) i, fun g => hi (.inr g)⟩⟩
  · rintro ⟨hl, hr⟩
    obtain ⟨hml, hil⟩ := (mem_sourceComparisonMarkChoices P t z.1).mp hl
    obtain ⟨hmr, hir⟩ := (mem_sourceComparisonMarkChoices Q u z.2).mp hr
    refine ⟨E.symm z, (mem_sourceComparisonMarkChoices (Sum.elim P Q) (Sum.elim t u) _).mpr
      ⟨?_, ?_⟩, E.apply_symm_apply z⟩
    · intro g i
      cases g with
      | inl g => exact hml g i
      | inr g => exact hmr g i
    · intro g
      cases g with
      | inl g => exact hil g
      | inr g => exact hir g

private theorem comparisonChoices_sum (P : G → Finset ℕ) (Q : H → Finset ℕ)
    (t : G → ℕ) (u : H → ℕ)
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ) (c : ((g : H) → Fin (u g) → ℕ) → ℂ) :
    (∑ l ∈ sourceComparisonMarkChoices (Sum.elim P Q) (Sum.elim t u),
      b (fun g => l (.inl g)) * c (fun g => l (.inr g))) =
      (∑ l ∈ sourceComparisonMarkChoices P t, b l) *
        (∑ r ∈ sourceComparisonMarkChoices Q u, c r) := by
  classical
  let E := comparisonChoicesSumEquiv t u
  calc
    _ = ∑ z ∈ (sourceComparisonMarkChoices (Sum.elim P Q) (Sum.elim t u)).map E.toEmbedding,
        b z.1 * c z.2 := (sum_map ..).symm
    _ = _ := by
      rw [comparisonChoices_sum_map P Q t u, sum_product, sum_mul]
      apply sum_congr rfl
      intro l _
      rw [mul_sum]

theorem sourceComparisonMarkWeight_sum (P : G → Finset ℕ) (Q : H → Finset ℕ)
    (t : G → ℕ) (u : H → ℕ) (q : G → ℝ) (r : H → ℝ)
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ) (c : ((g : H) → Fin (u g) → ℕ) → ℂ) (n : ℕ) :
    sourceComparisonMarkWeight (Sum.elim P Q) (Sum.elim t u) (Sum.elim q r)
      (fun l => b (fun g => l (.inl g)) * c (fun g => l (.inr g))) n =
      sourceComparisonMarkWeight P t q b n * sourceComparisonMarkWeight Q u r c n := by
  classical
  have hP : (fun g : G ⊕ H => activeDivisors (Sum.elim P Q g) n) =
      Sum.elim (fun g => activeDivisors (P g) n) (fun g => activeDivisors (Q g) n) := by
    funext g
    cases g <;> rfl
  unfold sourceComparisonMarkWeight
  rw [hP, comparisonChoices_sum]
  simp only [sourceComparisonMarkHitDamping, sourceComparisonMarkMass, Fintype.prod_sum_type,
    Sum.elim_inl, Sum.elim_inr, Complex.ofReal_mul, div_eq_mul_inv, mul_inv_rev]
  ring

private theorem comparisonChoices_constant_card (P : G → Finset ℕ) (a : ℕ) (ha : a ≤ 1) :
    (sourceComparisonMarkChoices P (fun _ => a)).card = ∏ g, (P g).card ^ a := by
  classical
  have he : sourceComparisonMarkChoices P (fun _ => a) = representedArrayChoices P (fun _ => a) := by
    unfold sourceComparisonMarkChoices
    apply filter_true_of_mem
    intro l _ g i j _
    have hi : (i : ℕ) < a := i.isLt
    have hj : (j : ℕ) < a := j.isLt
    exact Fin.ext (by omega)
  rw [he]
  simp only [representedArrayChoices, Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin]

theorem sourceComparisonMarkWeight_one (P : G → Finset ℕ) (q : G → ℝ) (n : ℕ) :
    sourceComparisonMarkWeight P (fun _ => 1) q (fun _ => 1) n =
      ((∏ g, (((bandCount (P g) n : ℝ) / bandReciprocalMass (P g)) *
        (q g) ^ (bandCount (P g) n - 1)) : ℝ) : ℂ) := by
  classical
  simp only [sourceComparisonMarkWeight, sum_const, nsmul_eq_mul, mul_one,
    comparisonChoices_constant_card _ 1 le_rfl, pow_one, sourceComparisonMarkHitDamping,
    sourceComparisonMarkMass, Nat.cast_prod, Complex.ofReal_prod, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast, prod_mul_distrib, prod_div_distrib, bandCount]
  ring

theorem sourceComparisonMarkWeight_zero (P : G → Finset ℕ) (q : G → ℝ) (n : ℕ) :
    sourceComparisonMarkWeight P (fun _ => 0) q (fun _ => 1) n =
      ((∏ g, (q g) ^ bandCount (P g) n : ℝ) : ℂ) := by
  classical
  simp only [sourceComparisonMarkWeight, sum_const, nsmul_eq_mul, mul_one,
    comparisonChoices_constant_card _ 0 (by omega), pow_zero, prod_const_one,
    Nat.cast_one, sourceComparisonMarkHitDamping, sourceComparisonMarkMass,
    Nat.sub_zero, Complex.ofReal_one, div_one]

theorem sourceComparisonMarkWeight_literal_inert (e : G → ℝ) (x : ℝ) (n : ℕ) :
    sourceComparisonMarkWeight (fun g => markedLogPowerBand (e g) x) (fun _ => 1)
      (fun _ => 1 / 2) (fun _ => 1) n = (literalMarkedArrayWeight e x n : ℂ) := by
  rw [sourceComparisonMarkWeight_one]
  apply congrArg Complex.ofReal
  unfold literalMarkedArrayWeight divisorWeight
  apply prod_congr rfl
  intro g _
  unfold bandWeight halfDampedCount
  ring

def sourceComparisonInertActiveMarks (e : G → ℝ) (x : ℝ)
    (P : H → Finset ℕ) (t : H → ℕ) (q : H → ℝ)
    (b : ((g : H) → Fin (t g) → ℕ) → ℂ) (n : ℕ) : ℂ :=
  sourceComparisonMarkWeight (Sum.elim (fun g => markedLogPowerBand (e g) x) P)
    (Sum.elim (fun _ => 1) t) (Sum.elim (fun _ => 1 / 2) q)
    (fun l => b (fun g => l (.inr g))) n

theorem sourceComparisonInertActiveMarks_eq (e : G → ℝ) (x : ℝ)
    (P : H → Finset ℕ) (t : H → ℕ) (q : H → ℝ)
    (b : ((g : H) → Fin (t g) → ℕ) → ℂ) (n : ℕ) :
    sourceComparisonInertActiveMarks e x P t q b n =
      (literalMarkedArrayWeight e x n : ℂ) * sourceComparisonMarkWeight P t q b n := by
  calc
    _ = sourceComparisonMarkWeight (fun g => markedLogPowerBand (e g) x) (fun _ => 1)
          (fun _ => 1 / 2) (fun _ => 1) n * sourceComparisonMarkWeight P t q b n := by
      simpa only [sourceComparisonInertActiveMarks, one_mul] using
        sourceComparisonMarkWeight_sum (fun g => markedLogPowerBand (e g) x) P
          (fun _ => 1) t (fun _ => 1 / 2) q (fun _ => 1) b n
    _ = _ := by rw [sourceComparisonMarkWeight_literal_inert]

end
end ArtinMatthews
