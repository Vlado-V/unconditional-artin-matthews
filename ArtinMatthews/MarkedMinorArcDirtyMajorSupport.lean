module

public import ArtinMatthews.MarkedMinorArcRawEdgeDetector
public import ArtinMatthews.MarkedMinorArcRawShiftGeometry


set_option backward.privateInPublic true
@[expose] public section

/-! Support is extracted from the actual major coefficient itself. A
nonzero full delta-minus-major coefficient is never assumed. -/
namespace ArtinMatthews
noncomputable section

 theorem markedRawEdgeChoiceDetectorCoefficient_support {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (η : ℝ → ℂ) (d₀ Y ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (detector : ℤ → ℤ → ℤ → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (choice : MarkedRawEdgeChoice hZ s)
    (hne : markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ detector s choice ≠ 0) :
    let D := markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1
    (d₀ ≤ (D:ℝ) ∧ (D:ℝ)<2*d₀) ∧ ((D:ℤ) ∣ markedMinorIntegerDet s.1.1 choice.target.1) ∧
      ¬MarkedRawFullCrossBan s.2.1 (markedRawEdgeTargetLast s.2.2 choice.promotions choice.fresh) ∧
      markedRawEndpointFactor hZ 1 χ s ≠ 0 ∧
      markedRawEndpointFactor hZ 1 χ (markedRawEdgeTargetState hZ s choice) ≠ 0 ∧
      detector (markedRawLastProduct ((markedRawActiveSplit pads) s.2.1).2)
        (markedRawLastProduct (markedRawEdgeTargetLast s.2.2 choice.promotions choice.fresh))
        (markedMinorIntegerDet s.1.1 choice.target.1/(D:ℤ)) ≠ 0 := by
  classical
  unfold markedRawEdgeChoiceDetectorCoefficient at hne
  dsimp only at hne ⊢
  split_ifs at hne with hdyad hdiv hban
  · exact False.elim (hne rfl)
  · simp only [mul_ne_zero_iff] at hne
    exact ⟨hdyad,hdiv,hban,hne.1.1.1.1.1.2,hne.2,hne.1.1.2⟩
  · exact False.elim (hne rfl)
  · exact False.elim (hne rfl)

 theorem markedDirtyMajor_source_shear {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (η ψ : ℝ → ℂ) (r d₀ Y Q ρ : ℝ)
    (w : Z → ℤ × ℤ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (choice : MarkedRawEdgeChoice hZ s)
    (hne : markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ
      (markedRawFirstGoodCutoff r d₀ Y w χ) (markedRawEdgeMajorDetector ψ Q Y) s choice ≠ 0) :
    MarkedMinorShearGood ((markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1:ℝ)*
      markedMinorIntegerTau r (w s.1)/markedMinorIntegerTau r s.1.1) Y := by
  have hs := markedRawEdgeChoiceDetectorCoefficient_support hZ η d₀ Y ρ _ _ s choice hne
  have hg := markedRawFirstGoodCutoff_ne_zero r d₀ Y w χ s
    (markedRawEndpointFactor_ne_zero_test hZ 1 _ s hs.2.2.2.1)
  exact markedRawFirstGood_clean_shear r d₀ Y w s hg hs.1

 theorem markedDirtyMajor_shared_squarefree {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (hP : Pairwise (fun i j => Disjoint (P i) (P j)))
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (η ψ : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (choice : MarkedRawEdgeChoice hZ s)
    (hne : markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ
      (markedRawEdgeMajorDetector ψ Q Y) s choice ≠ 0) :
    Squarefree (markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1) := by
  have hs := markedRawEdgeChoiceDetectorCoefficient_support hZ η d₀ Y ρ χ _ s choice hne
  exact markedRawCopiedProduct_squarefree_of_fullDistinct hP pads s.2.1
    (markedRawEndpointFactor_ne_zero_distinct hZ 1 χ s hs.2.2.2.1)

 theorem markedDirtyMajor_cutoff_support {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (η ψ : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (choice : MarkedRawEdgeChoice hZ s)
    (hne : markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ
      (markedRawEdgeMajorDetector ψ Q Y) s choice ≠ 0) :
    ψ (((markedMinorIntegerDet s.1.1 choice.target.1/
      (markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1:ℤ):ℤ):ℝ)/Y) ≠ 0 := by
  have hs := markedRawEdgeChoiceDetectorCoefficient_support hZ η d₀ Y ρ χ _ s choice hne
  exact (mul_ne_zero_iff.mp hs.2.2.2.2.2).1

end
end ArtinMatthews
