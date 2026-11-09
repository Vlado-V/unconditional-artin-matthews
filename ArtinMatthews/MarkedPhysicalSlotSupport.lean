module

public import ArtinMatthews.MarkedFiniteSingleSlotExchange
public import ArtinMatthews.MarkedPhysicalRawMatrixEntry
public import ArtinMatthews.MarkedPhysicalMatrixPairing


set_option backward.privateInPublic true
@[expose] public section

/-! The actual copied-prefix and full-cross-ban tests imply the genuine
single-slot exchange after the two physical slot permutations. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Classical
noncomputable section
attribute [local instance] Classical.propDecidable

theorem markedRawJoint_ne_zero_not_banned
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s t : MarkedRawState P (pads+1) B Z)
    (h : markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ s t≠0) :
    ¬MarkedRawFullCrossBan s.2.1 ((markedRawActiveSplit pads) t.2.1).2 := by
  unfold markedRawEdgeJointCoefficient at h
  dsimp only at h
  split_ifs at h with hd hv hb
  · exact False.elim (h rfl)
  · exact hb
  · exact False.elim (h rfl)
  · exact False.elim (h rfl)

theorem markedPhysicalPermutedEdge_exchange
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (s t : MarkedPhysicalState P (pads+1) Z)
    (σ τ : J → Equiv.Perm (Fin (pads+1)))
    (h : markedPhysicalEdgeMatrix P hP V pads Z hZ ψ η d₀ Y Q q
      (markedPhysicalSlotEquiv P (pads+1) Z σ s) (markedPhysicalSlotEquiv P (pads+1) Z τ t)≠0) :
    let a := (markedPhysicalStateToRaw P hP (pads+1) Z s).2.1
    let b := (markedPhysicalStateToRaw P hP (pads+1) Z t).2.1
    (∀ j,¬∃ k,a j k=b j (τ j (Fin.last pads))) ∧
      (∀ j x,(∃ k,b j k=x) ↔
        ((∃ k,a j k=x) ∧ x≠a j (σ j (Fin.last pads))) ∨ x=b j (τ j (Fin.last pads))) := by
  let a := (markedPhysicalStateToRaw P hP (pads+1) Z s).2.1
  let b := (markedPhysicalStateToRaw P hP (pads+1) Z t).2.1
  change (∀ j,¬∃ k,a j k=b j (τ j (Fin.last pads))) ∧ _
  have hh := markedPhysicalEdgeMatrix_ne_zero_guards P hP V pads Z hZ ψ η d₀ Y Q q
    (markedPhysicalSlotEquiv P (pads+1) Z σ s) (markedPhysicalSlotEquiv P (pads+1) Z τ t) h
  dsimp only at hh
  have hcopy (j : J) (k : Fin pads) : a j (σ j k.castSucc)=b j (τ j k.castSucc) :=
    congrFun (congrFun hh.1 j) k
  have hban := markedRawJoint_ne_zero_not_banned hZ ψ η d₀ Y Q 1 (fun _ => 1) _ _ hh.2
  constructor
  · intro j hbad
    obtain ⟨k,hk⟩ := hbad
    apply hban
    refine ⟨j,j,(σ j).symm k,?_⟩
    change (b j (τ j (Fin.last pads))).1=(a j (σ j ((σ j).symm k))).1
    rw [Equiv.apply_symm_apply]
    exact congrArg Subtype.val hk.symm
  · intro j x
    exact markedPermutedSingleSlotExchange pads (a j) (b j)
      (markedPhysicalStateToRaw_distinct P hP (pads+1) Z s j) (σ j) (τ j) (hcopy j) x

end
end ArtinMatthews
