module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import ArtinMatthews.MarkedArrayExpansion
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Two omitted layers and the represented labels are counted by their
actual union. The two subsets may overlap and the represented labels may
repeat. -/

noncomputable section
namespace ArtinMatthews

open scoped BigOperators

theorem cubicSampling_tail_union_count (P : Finset ℕ) (s h : ℕ) :
    P.card ^ s * (P.card.choose h) ^ 2 ≤
      ∑ k ∈ Finset.Icc h (2 * h + s), k ^ s * 4 ^ k * P.card.choose k := by
  classical
  let S := Fintype.piFinset (fun _ : Fin s => P) ×ˢ (P.powersetCard h ×ˢ P.powersetCard h)
  let fiber (Q : Finset ℕ) :=
    Fintype.piFinset (fun _ : Fin s => Q) ×ˢ (Q.powerset ×ˢ Q.powerset)
  let U := (Finset.Icc h (2 * h + s)).sigma (fun k => (P.powersetCard k).sigma fiber)
  let union (t : (Fin s → ℕ) × (Finset ℕ × Finset ℕ)) :=
    representedChoiceSet t.1 ∪ t.2.1 ∪ t.2.2
  let f (t : (Fin s → ℕ) × (Finset ℕ × Finset ℕ)) :
      Σ _k : ℕ, Σ _Q : Finset ℕ, (Fin s → ℕ) × (Finset ℕ × Finset ℕ) :=
    ⟨(union t).card, union t, t⟩
  calc
    _ = S.card := by
      simp only [S, Finset.card_product, Fintype.card_piFinset, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin, Finset.card_powersetCard, pow_two]
    _ ≤ U.card := by
      apply Finset.card_le_card_of_injOn f
      · intro t ht
        obtain ⟨ht₀, htT⟩ := Finset.mem_product.mp ht
        obtain ⟨ht₁, ht₂⟩ := Finset.mem_product.mp htT
        obtain ⟨h₁, hc₁⟩ := Finset.mem_powersetCard.mp ht₁
        obtain ⟨h₂, hc₂⟩ := Finset.mem_powersetCard.mp ht₂
        have h₀ : representedChoiceSet t.1 ⊆ P :=
          representedChoiceSet_subset (Fintype.mem_piFinset.mp ht₀)
        have hs : (representedChoiceSet t.1).card ≤ s :=
          Finset.card_image_le.trans_eq (by simp)
        have hc : (union t).card ≤ 2 * h + s := by
          calc
            _ ≤ (representedChoiceSet t.1 ∪ t.2.1).card + t.2.2.card := Finset.card_union_le _ _
            _ ≤ (representedChoiceSet t.1).card + t.2.1.card + t.2.2.card :=
              Nat.add_le_add_right (Finset.card_union_le _ _) _
            _ ≤ _ := by omega
        have hlow : h ≤ (union t).card := hc₂ ▸ Finset.card_le_card Finset.subset_union_right
        refine Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hlow, hc⟩,
          Finset.mem_sigma.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, rfl⟩, ?_⟩⟩
        · exact Finset.union_subset (Finset.union_subset h₀ h₁) h₂
        · refine Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr ?_,
            Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr ?_, Finset.mem_powerset.mpr ?_⟩⟩
          · intro i
            exact Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
          · exact Finset.subset_union_right.trans Finset.subset_union_left
          · exact Finset.subset_union_right
      · intro t _ht u _hu htu
        exact congrArg (fun p : Σ _k : ℕ, Σ _Q : Finset ℕ,
          (Fin s → ℕ) × (Finset ℕ × Finset ℕ) => p.2.2) htu
    _ = _ := by
      dsimp only [U]
      rw [Finset.card_sigma]
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.card_sigma]
      have hf (Q : Finset ℕ) (hQ : Q ∈ P.powersetCard k) :
          (fiber Q).card = k ^ s * 4 ^ k := by
        simp only [fiber, Finset.card_product, Fintype.card_piFinset, Finset.prod_const,
          Finset.card_univ, Fintype.card_fin, Finset.card_powerset, (Finset.mem_powersetCard.mp hQ).2]
        rw [← mul_pow]
        norm_num
      rw [Finset.sum_congr rfl hf, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul, mul_comm]
      rfl

end ArtinMatthews
