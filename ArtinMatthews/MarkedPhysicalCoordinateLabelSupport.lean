module

public import ArtinMatthews.MarkedPhysicalCoordinateIndexCoefficient
public import ArtinMatthews.MarkedFiniteSingleSlotExchange


set_option backward.privateInPublic true
@[expose] public section

/-! The actual pure-label coefficient support gives the literal shared
prefix and cross-ban exclusion, hence the genuine active-prime exchange.
No supported physical root is needed for these arithmetic facts. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

theorem markedPhysicalCoordinateKernel_ne_zero_guards
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (V : J → ℝ) (pads : ℕ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
    (source target : MarkedRawActive P (pads+1)) (z z' : ℤ × ℤ)
    (h : markedPhysicalCoordinateKernel V pads ψ η d₀ Y Q source target z z'≠0) :
    ((markedRawActiveSplit pads) source).1=((markedRawActiveSplit pads) target).1 ∧
      ¬MarkedRawFullCrossBan source ((markedRawActiveSplit pads) target).2 := by
  unfold markedPhysicalCoordinateKernel at h
  dsimp only at h
  split_ifs at h with hp hd hv hb
  · exact False.elim (h (by simp only [mul_zero]))
  · exact ⟨hp,hb⟩
  · exact False.elim (h (by simp only [mul_zero]))
  · exact False.elim (h (by simp only [mul_zero]))
  · exact False.elim (h (by simp only [mul_zero]))

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ) (pads : ℕ)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)

theorem markedPhysicalCoordinateLabelCopy_exchange (j : ℕ)
    (a b : MarkedPhysicalMarking P (pads+1)) (ha : MarkedPhysicalMarkingDistinct a)
    (c : (J → Equiv.Perm (Fin (pads+1))) × (J → Equiv.Perm (Fin (pads+1))))
    (z z' : ℤ × ℤ)
    (h : markedPhysicalCoordinateLabelCopy P hP V pads ψ η d₀ Y Q j a b c z z'≠0) :
    let a₀ := (markedPhysicalMarkingEquiv P hP (pads+1)).symm a
    let b₀ := (markedPhysicalMarkingEquiv P hP (pads+1)).symm b
    (∀ i,¬∃ k,a₀ i k=b₀ i (c.2 i (Fin.last pads))) ∧
      (∀ i x,(∃ k,b₀ i k=x) ↔
        ((∃ k,a₀ i k=x) ∧ x≠a₀ i (c.1 i (Fin.last pads))) ∨ x=b₀ i (c.2 i (Fin.last pads))) := by
  let a₀ := (markedPhysicalMarkingEquiv P hP (pads+1)).symm a
  let b₀ := (markedPhysicalMarkingEquiv P hP (pads+1)).symm b
  let as := (markedPhysicalMarkingEquiv P hP (pads+1)).symm (fun i k => a i (c.1 i k))
  let bs := (markedPhysicalMarkingEquiv P hP (pads+1)).symm (fun i k => b i (c.2 i k))
  have hguards : ((markedRawActiveSplit pads) as).1=((markedRawActiveSplit pads) bs).1 ∧
      ¬MarkedRawFullCrossBan as ((markedRawActiveSplit pads) bs).2 := by
    by_cases hj : j%2=0
    · apply markedPhysicalCoordinateKernel_ne_zero_guards V pads ψ η d₀ Y Q as bs z z'
      intro hz
      dsimp only [as,bs] at hz
      exact h (by simp only [markedPhysicalCoordinateLabelCopy,hj,ite_true,hz,mul_zero])
    · apply markedPhysicalCoordinateKernel_ne_zero_guards V pads (markedRawEdgeAdjointCutoff ψ)
        (fun u => star (η u)) d₀ Y Q as bs z z'
      intro hz
      dsimp only [as,bs] at hz
      exact h (by simp only [markedPhysicalCoordinateLabelCopy,hj,ite_false,hz,mul_zero])
  have hcopy (i : J) (k : Fin pads) : a₀ i (c.1 i k.castSucc)=b₀ i (c.2 i k.castSucc) :=
    congrFun (congrFun hguards.1 i) k
  have hai : MarkedRawActiveDistinct a₀ :=
    (markedPhysicalMarkingEquiv_distinct P hP (pads+1) a₀).mp (by
      simpa only [a₀,Equiv.apply_symm_apply] using ha)
  constructor
  · intro i hbad
    obtain ⟨k,hk⟩ := hbad
    apply hguards.2
    refine ⟨i,i,(c.1 i).symm k,?_⟩
    change (b₀ i (c.2 i (Fin.last pads))).1=(a₀ i (c.1 i ((c.1 i).symm k))).1
    rw [Equiv.apply_symm_apply]
    exact congrArg Subtype.val hk.symm
  · intro i x
    exact markedPermutedSingleSlotExchange pads (a₀ i) (b₀ i) (hai i) (c.1 i) (c.2 i) (hcopy i) x

end
end ArtinMatthews
