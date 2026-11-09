module

public import ArtinMatthews.MarkedTypeIISharedMajorFinite
public import ArtinMatthews.MarkedMajorFixedCharacterInterval


set_option backward.privateInPublic true
@[expose] public section

/-! The literal scalar interval sums split into the coprime-label
component used by the physical lift and the shared-label correction. -/
namespace ArtinMatthews
noncomputable section
open Finset
open scoped ComplexConjugate
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] (P : J → Finset ℕ)
  (η : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) (Q Y W modulation : ℝ)
  (S T : Finset ℕ) (l r : ℕ) (β : ℕ → ℂ)

def markedMajorDyadPairSum (E : (ℕ×ℕ) → Prop) : ℂ :=
  markedTypeIIScalarMajorOn P
    ((markedTypeIIDyadLabels P Y×ˢmarkedTypeIIDyadLabels P Y).filter E)
    S T (Icc l r) η ψ Q Y (markedMajorCenteredCoefficient W modulation) β
    (fun _ _ _ => 1)

def markedMajorFixedDyadPairSum {Mχ : ℕ} (ξ : DirichletCharacter ℂ Mχ)
    (E : (ℕ×ℕ) → Prop) : ℂ :=
  markedTypeIIScalarMajorOn P
    ((markedTypeIIDyadLabels P Y×ˢmarkedTypeIIDyadLabels P Y).filter E)
    S T (Icc l r) η ψ Q Y (markedMajorCenteredCoefficient W modulation) β
    (fun _ v w => ξ (v.1*v.2:ℕ)*conj (ξ (w.1*w.2:ℕ)))

theorem markedMajorIntervalPairSum_eq_coprime_add_shared
    (hY : 0 < Y) (hη : Function.support η ⊆ Set.Icc 1 4) :
    markedMajorIntervalPairSum P η ψ Q Y W modulation S T l r β =
      markedMajorDyadPairSum P η ψ Q Y W modulation S T l r β (fun z => z.1.Coprime z.2)+
      markedMajorDyadPairSum P η ψ Q Y W modulation S T l r β (fun z => ¬ z.1.Coprime z.2) := by
  let α := markedMajorCenteredCoefficient W modulation
  let G : (ℕ×ℕ) → (ℕ×ℕ) → (ℕ×ℕ) → ℂ := fun _ _ _ => 1
  have h := markedTypeIIScalarMajorOn_label_sum P S T (Icc l r) η ψ Q Y α β G
  have he : markedMajorIntervalPairSum P η ψ Q Y W modulation S T l r β =
      markedTypeIIScalarMajorOn P (markedMajorLabelSet P×ˢmarkedMajorLabelSet P)
        S T (Icc l r) η ψ Q Y α β G := by
    rw [h]
    simp only [G,α,one_mul,markedTypeIIScalarMajorTerm,markedMajorIntervalPairSum]
  rw [he,markedTypeIIScalarMajorOn_dyad P S T (Icc l r) η ψ Q Y hY hη]
  dsimp only [markedMajorDyadPairSum,markedTypeIIScalarMajorOn,α,G]
  rw [← mul_add,sum_filter,sum_filter,← sum_add_distrib]
  apply congrArg (fun x : ℂ => (markedMajorLabelMass P:ℂ)^2*x)
  apply sum_congr rfl
  intro z _
  by_cases hz : z.1.Coprime z.2
  · have hzn : ¬¬z.1.Coprime z.2 := fun hn => hn hz
    simp only [ite_eq_left hz,ite_eq_right hzn,add_zero]
  · simp only [ite_eq_right hz,ite_eq_left hz,zero_add]

theorem markedMajorFixedIntervalPairSum_eq_coprime_add_shared
    {Mχ : ℕ} (ξ : DirichletCharacter ℂ Mχ)
    (hY : 0 < Y) (hη : Function.support η ⊆ Set.Icc 1 4) :
    markedMajorFixedIntervalPairSum P ξ η ψ Q Y W modulation S T l r β =
      markedMajorFixedDyadPairSum P η ψ Q Y W modulation S T l r β ξ (fun z => z.1.Coprime z.2)+
      markedMajorFixedDyadPairSum P η ψ Q Y W modulation S T l r β ξ (fun z => ¬ z.1.Coprime z.2) := by
  let α := markedMajorCenteredCoefficient W modulation
  let G : (ℕ×ℕ) → (ℕ×ℕ) → (ℕ×ℕ) → ℂ :=
    fun _ v w => ξ (v.1*v.2:ℕ)*conj (ξ (w.1*w.2:ℕ))
  have he : markedMajorFixedIntervalPairSum P ξ η ψ Q Y W modulation S T l r β =
      markedTypeIIScalarMajorOn P (markedMajorLabelSet P×ˢmarkedMajorLabelSet P)
        S T (Icc l r) η ψ Q Y α β G := by
    rw [markedTypeIIScalarMajorOn_label_sum]
    unfold markedMajorFixedIntervalPairSum
    apply congrArg (fun x : ℂ => (markedMajorLabelMass P:ℂ)^2*x)
    apply sum_congr rfl
    intro b _
    apply sum_congr rfl
    intro m _
    apply sum_congr rfl
    intro n _
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro u _
    apply sum_congr rfl
    intro v _
    dsimp only [G,α,markedTypeIIScalarMajorTerm]
    simp only [Nat.cast_mul]
    ring
  rw [he,markedTypeIIScalarMajorOn_dyad P S T (Icc l r) η ψ Q Y hY hη]
  dsimp only [markedMajorFixedDyadPairSum,markedTypeIIScalarMajorOn,α,G]
  rw [← mul_add,sum_filter,sum_filter,← sum_add_distrib]
  apply congrArg (fun x : ℂ => (markedMajorLabelMass P:ℂ)^2*x)
  apply sum_congr rfl
  intro z _
  by_cases hz : z.1.Coprime z.2
  · have hzn : ¬¬z.1.Coprime z.2 := fun hn => hn hz
    simp only [ite_eq_left hz,ite_eq_right hzn,add_zero]
  · simp only [ite_eq_right hz,ite_eq_left hz,zero_add]

theorem markedMajorIntervalPairSum_sub_coprime
    (hY : 0 < Y) (hη : Function.support η ⊆ Set.Icc 1 4) :
    markedMajorIntervalPairSum P η ψ Q Y W modulation S T l r β -
      markedMajorDyadPairSum P η ψ Q Y W modulation S T l r β (fun z => z.1.Coprime z.2) =
      markedMajorDyadPairSum P η ψ Q Y W modulation S T l r β (fun z => ¬ z.1.Coprime z.2) := by
  rw [markedMajorIntervalPairSum_eq_coprime_add_shared P η ψ Q Y W modulation S T l r β hY hη]
  exact add_sub_cancel_left _ _

theorem markedMajorFixedIntervalPairSum_sub_coprime
    {Mχ : ℕ} (ξ : DirichletCharacter ℂ Mχ)
    (hY : 0 < Y) (hη : Function.support η ⊆ Set.Icc 1 4) :
    markedMajorFixedIntervalPairSum P ξ η ψ Q Y W modulation S T l r β -
      markedMajorFixedDyadPairSum P η ψ Q Y W modulation S T l r β ξ (fun z => z.1.Coprime z.2) =
      markedMajorFixedDyadPairSum P η ψ Q Y W modulation S T l r β ξ (fun z => ¬ z.1.Coprime z.2) := by
  rw [markedMajorFixedIntervalPairSum_eq_coprime_add_shared P η ψ Q Y W modulation S T l r β ξ hY hη]
  exact add_sub_cancel_left _ _

end
end ArtinMatthews
