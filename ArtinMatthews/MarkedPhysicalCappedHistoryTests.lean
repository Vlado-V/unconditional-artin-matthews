module

public import ArtinMatthews.MarkedPhysicalCappedHistoryFunctional
public import ArtinMatthews.MarkedMemoryStageTests


set_option backward.privateInPublic true
@[expose] public section

/-! The exact alternating coordinate/history join with arbitrary original
endpoint cutoffs and complete-history tests. No symmetry or constancy of
these tests is assumed; their actual ordered arguments remain visible. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime)
  (hdis : ∀ j k,j≠k → Disjoint (markedRawPrimeBand (P j)) (markedRawPrimeBand (P k)))
  {pads B R n : ℕ}
  (hZ : ∀ z∈markedPrimitiveCoordinateTube R,IsCoprime z.1 z.2)
  (V : J → ℝ) (hV : ∀ j,V j≠0) (q : ℝ)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
  (s : MarkedRawState (fun j => markedRawPrimeBand (P j)) (pads+1) B (markedPrimitiveCoordinateTube R))
  (hs : s.1.1=(1,0)) (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)

include hV hs hempty in
theorem markedPhysicalCappedHistory_test_functional
    (ρ : ℝ) (hρ : ρ≠0)
    (χ : ℕ → MarkedRawState (fun j => markedRawPrimeBand (P j)) (pads+1) B
      (markedPrimitiveCoordinateTube R) → ℂ)
    (F : MarkedMemoryChronologicalHistory hZ n s → ℂ) :
    (markedRawStateMass (markedMemoryTiltAtoms V q n) s:ℂ)*
      (∑ H : MarkedMemoryPrimeSupportedHistory (n := n) hZ s,
        markedMemoryGeometricHistoryWeight (markedMemoryTiltAtoms V q n) V hZ ψ η d₀ Y Q ρ
          markedMemoryAlternatingOrientation (markedMemoryHistoryVisitSchedule q n) χ n 0 H.1 * F H.1)=
      (markedPhysicalMass V (pads+1):ℂ)*
        ∑ i : MarkedMemoryCappedPathDecoratedIndex (n := n) hZ s,
          ((markedMemoryPathPrimeChoiceWeight hZ i.1.path q i.1.choices /
            markedMemoryIndependentBirthFactorials hZ
              (markedMemoryCappedPathIndependent (B := B) hZ i.1.path i.1.choices
                i.1.compatible i.1.capacity i.2.1):ℝ):ℂ)*
          markedPhysicalCoordinateIndexCoefficient P hP V pads ψ η d₀ Y Q
            (markedPhysicalMemoryHistoryIndex P hP hZ (markedMemoryCappedPathDecoratedAssembly hZ hdis s i))*
          (markedMemoryStageTestProduct hZ
            (fun k => if markedMemoryAlternatingOrientation k then fun u => star (χ k u) else χ k)
            n 0 (markedMemoryCappedPathDecoratedAssembly hZ hdis s i)*
            F (markedMemoryCappedPathDecoratedAssembly hZ hdis s i)) := by
  have hh := markedPhysicalCappedHistory_functional P hP hdis hZ V hV q ψ η d₀ Y Q s hs hempty ρ hρ
    (fun H => markedMemoryStageTestProduct hZ
      (fun k => if markedMemoryAlternatingOrientation k then fun u => star (χ k u) else χ k) n 0 H*F H)
  apply Eq.trans ?_ hh
  congr 1
  apply Finset.sum_congr rfl
  intro H _
  rw [markedMemoryGeometricHistoryWeight_test_factor]
  ring

end
end ArtinMatthews
