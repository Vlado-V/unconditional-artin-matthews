module

public import ArtinMatthews.MarkedPhysicalCoordinateIndexCoefficient
public import ArtinMatthews.MarkedPhysicalCoordinateTermSums
public import ArtinMatthews.MarkedPhysicalMomentFiniteCoordinates


set_option backward.privateInPublic true
@[expose] public section

/-! The original guarded physical path weight is expanded per slot
copy before summing over the literal finite coordinate index. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ)
  (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)

def markedPhysicalMomentCopyPathTerm
    (G : MarkedPhysicalState P (pads+1) Z → Prop) (n : ℕ)
    (p : Fin (n+1) → MarkedPhysicalState P (pads+1) Z)
    (copies : Fin n → (J → Equiv.Perm (Fin (pads+1))) × (J → Equiv.Perm (Fin (pads+1)))) : ℂ :=
  if (p 0).1.1=(p (Fin.last n)).1.1 ∧ (∀ v,G (p v)) then
    ∏ v : Fin n,markedPhysicalMomentGeometricCopy P hP V pads Z hZ ψ η d₀ Y Q q
      v.val (p v.castSucc) (p v.succ) (copies v)
  else 0

def markedPhysicalCoordinateIndexTerm
    (G : MarkedPhysicalState P (pads+1) Z → Prop) {n B : ℕ}
    (i : MarkedPhysicalCoordinateIndex P (pads+1) n B)
    {S : ℕ} {A B' C D : ℝ} (r : MarkedPhysicalCanonicalRoot S A B' C D) : ℂ :=
  markedPhysicalPathCoordinateTerm
    (fun p => markedPhysicalMomentCopyPathTerm P hP V pads Z hZ ψ η d₀ Y Q q G n p i.2.2)
    i.1 r (fun v => (i.2.1 v).1)

theorem markedPhysicalMomentPathTerm_sum_copies
    (G : MarkedPhysicalState P (pads+1) Z → Prop) (R : ℕ)
    (p : MarkedPhysicalMomentPath P (pads+1) Z R) :
    markedPhysicalMomentPathTerm P hP V pads Z hZ ψ η d₀ Y Q q G R p=
      ∑ copies : Fin (2*R) → (J → Equiv.Perm (Fin (pads+1))) × (J → Equiv.Perm (Fin (pads+1))),
        markedPhysicalMomentCopyPathTerm P hP V pads Z hZ ψ η d₀ Y Q q G (2*R) p copies := by
  by_cases h : (p 0).1.1=(p (Fin.last (2*R))).1.1 ∧ (∀ v,G (p v))
  · simp only [markedPhysicalMomentPathTerm,markedPhysicalMomentCopyPathTerm,ite_eq_left h]
  · simp only [markedPhysicalMomentPathTerm,markedPhysicalMomentCopyPathTerm,ite_eq_right h,
      Finset.sum_const_zero]

theorem markedPhysicalMomentCoordinateTerm_sum_copies
    (G : MarkedPhysicalState P (pads+1) Z → Prop) (R B : ℕ)
    (a : MarkedPhysicalLabelPath P (pads+1) (2*R))
    (tail : Fin (2*R) → ↥(markedPrimitiveCoordinateTube B))
    {S : ℕ} {A B' C D : ℝ} (r : MarkedPhysicalCanonicalRoot S A B' C D) :
    markedPhysicalPathCoordinateTerm
      (markedPhysicalMomentPathTerm P hP V pads Z hZ ψ η d₀ Y Q q G R) a r (fun v => (tail v).1)=
      ∑ copies : Fin (2*R) → (J → Equiv.Perm (Fin (pads+1))) × (J → Equiv.Perm (Fin (pads+1))),
        markedPhysicalCoordinateIndexTerm P hP V pads Z hZ ψ η d₀ Y Q q G (a,tail,copies) r := by
  have hf : markedPhysicalMomentPathTerm P hP V pads Z hZ ψ η d₀ Y Q q G R=
      (fun p => ∑ copies : Fin (2*R) →
        (J → Equiv.Perm (Fin (pads+1))) × (J → Equiv.Perm (Fin (pads+1))),
        markedPhysicalMomentCopyPathTerm P hP V pads Z hZ ψ η d₀ Y Q q G (2*R) p copies) := by
    funext p
    exact markedPhysicalMomentPathTerm_sum_copies P hP V pads Z hZ ψ η d₀ Y Q q G R p
  rw [hf]
  exact markedPhysicalPathCoordinateTerm_sum_weights _ a r _

end
end ArtinMatthews
