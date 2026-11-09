module

public import ArtinMatthews.MarkedMemoryCappedPathAssembly
public import ArtinMatthews.MarkedMemoryIndependentChoiceWeightTotal
public import ArtinMatthews.MarkedMemoryPathOrphanTailData
public import ArtinMatthews.MarkedMemoryWeightTransport


set_option backward.privateInPublic true
@[expose] public section

/-! The actual capped path coefficient has exactly the original tilted
source normalization, the primewise signed choice product and the
literal ordered raw residual. Initial atoms remain outside W. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] [hJ : DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (hP : ∀ i j,i≠j → Disjoint (P i) (P j))
  (s : MarkedRawState P (pads+1) B Z)
  (i : MarkedMemoryCappedPathDecoratedIndex (n := n) hZ s)

omit [DecidableEq J] in
theorem markedMemoryCappedPath_choiceProduct (q : ℝ) :
    markedMemoryIndependentPrimeChoiceProduct hZ
      (markedMemoryCappedPathIndependent (B := B) hZ i.1.path i.1.choices i.1.compatible i.1.capacity i.2.1)
      (markedMemoryCappedPathIndependent_prime_injective (B := B) hZ i.1.path i.1.choices i.1.compatible i.1.capacity i.2.1 hP)
      q (markedMemoryLineAtoms (P := P) q n)=markedMemoryPathPrimeChoiceWeight hZ i.1.path q i.1.choices := by
  unfold markedMemoryIndependentPrimeChoiceProduct markedMemoryIndependentPrimeChoiceFactor
  rw [markedMemoryCappedPathIndependent_path (B := B) hZ i.1.path i.1.choices i.1.compatible i.1.capacity i.2.1 hP,
    markedMemoryCappedPathIndependent_choices (B := B) hZ i.1.path i.1.choices i.1.compatible i.1.capacity i.2.1 hP]
  rfl

theorem markedMemoryCappedPath_tilt_coefficient
    (V : J → ℝ) (hV : ∀ j,V j≠0) (q : ℝ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) :
    (markedRawStateMass (markedMemoryTiltAtoms (P := P) V q n) s:ℂ)*
      markedMemoryChronologicalWeight (markedMemoryTiltAtoms (P := P) V q n) V hZ ψ η d₀ Y Q 1
        (markedMemoryHistoryVisitSchedule q n) χ n 0 (markedMemoryCappedPathDecoratedAssembly hZ hP s i)=
      (markedPhysicalMass V (pads+1):ℂ)*(((∏ j,(V j)⁻¹:ℝ):ℂ)^n)*
        ((markedMemoryPathPrimeChoiceWeight hZ i.1.path q i.1.choices/
          markedMemoryIndependentBirthFactorials hZ
            (markedMemoryCappedPathIndependent (B := B) hZ i.1.path i.1.choices i.1.compatible i.1.capacity i.2.1):ℝ):ℂ)*
        markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n 0
          (markedMemoryCappedPathDecoratedAssembly hZ hP s i) := by
  have hdec : hJ=Classical.decEq J := Subsingleton.elim _ _
  cases hdec
  let raw := markedMemoryCappedPathIndependent (B := B) hZ i.1.path i.1.choices i.1.compatible i.1.capacity i.2.1
  let hs := (markedMemoryCappedPathIndependent_source hZ hP i.1.path i.1.choices i.1.compatible i.1.capacity i.2.1).trans i.1.source
  have hw := markedMemoryIndependent_tilt_choice_source_weight_all hZ raw
    (markedMemoryCappedPathIndependent_prime_injective (B := B) hZ i.1.path i.1.choices i.1.compatible i.1.capacity i.2.1 hP)
    (markedMemoryCappedPathIndependent_initial (B := B) hZ i.1.path i.1.choices i.1.compatible i.1.capacity i.2.1)
    (markedMemoryCappedPathIndependent_terminal (B := B) hZ i.1.path i.1.choices i.1.compatible i.1.capacity i.2.1)
    (markedMemoryCappedPathIndependent_normalized (B := B) hZ i.1.path i.1.choices i.1.compatible i.1.capacity i.2.1)
    i.2.2 ψ η d₀ Y Q χ V hV q
  rw [markedMemoryCappedPath_choiceProduct hZ hP s i q] at hw
  have hm := congrArg (fun u => (markedRawStateMass (markedMemoryTiltAtoms (P := P) V q n) u:ℂ)) hs
  have ht := markedMemoryChronologicalWeight_transport hZ ψ η d₀ Y Q hs
    (markedMemoryIndependentHistory hZ raw i.2.2) (markedMemoryTiltAtoms (P := P) V q n) V 1
    (markedMemoryHistoryVisitSchedule q n) χ 0
  have hr := markedMemoryHistoryEdgeResidual_transport hZ ψ η d₀ Y Q hs
    (markedMemoryIndependentHistory hZ raw i.2.2) χ 0
  exact (congrArg₂ (fun a b : ℂ => a*b) hm.symm ht).trans
    (hw.trans (congrArg (fun z => (markedPhysicalMass V (pads+1):ℂ)*(((∏ j,(V j)⁻¹:ℝ):ℂ)^n)*
      ((markedMemoryPathPrimeChoiceWeight hZ i.1.path q i.1.choices/
        markedMemoryIndependentBirthFactorials hZ raw:ℝ):ℂ)*z) hr.symm))

end
end ArtinMatthews
