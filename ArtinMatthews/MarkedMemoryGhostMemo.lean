module

public import ArtinMatthews.MarkedMemoryHistoryLifespanScalar
public import ArtinMatthews.MarkedMemoryPrefixMemo
public import ArtinMatthews.MarkedMemoryStageBirthMass
public import ArtinMatthews.MarkedMemoryHistoryPotentialAccess
public import ArtinMatthews.MarkedMemoryStageMemo
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! Initial active labels and literal ordered ghost births produce the
actual history memo. Unperformed ghost slots are proved absent, rather
than assigned a prime or removed from the potential-address carrier. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}

theorem markedMemoryHistoryMemo_initial
    (history : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryStageBirthValues 0 (markedMemoryHistoryMemo hZ history 0)
      markedMemoryInitialDraw markedMemoryInitialDraw_injective
      (fun a : Σ _j : J,Fin (pads+1) => s.2.1 a.1 a.2)=
        markedMemoryHistoryMemo hZ history 1 := by
  classical
  apply markedMemoryStageBirthValues_memo
  · intro a
    rfl
  · intro a
    rfl
  · intro a ht hn
    rcases a with ⟨j,k⟩ | ⟨t,j,k⟩ | ⟨t,j⟩
    · exact False.elim (hn (markedMemoryStageDraw_mem
        markedMemoryInitialDraw markedMemoryInitialDraw_injective ⟨j,k⟩))
    · simp only [markedMemoryPotentialChronologicalTime] at ht
      omega
    · simp only [markedMemoryPotentialChronologicalTime] at ht
      omega

theorem markedMemoryHistoryMemo_ghost
    (history : MarkedMemoryChronologicalHistory hZ n s) (v : Fin (n+1)) :
    let ghost := markedMemoryHistoryVertexGhost hZ history v
    markedMemoryStageBirthValues (2*v.val+1) (markedMemoryHistoryMemo hZ history (2*v.val+1))
      (markedMemoryGhostStageDraw v ghost.sizes.1)
      (markedMemoryGhostStageDraw_injective v ghost.sizes.1)
      (fun a : Σ j,Fin (ghost.sizes.1 j:ℕ) => ghost.births a.1 a.2)=
        markedMemoryHistoryMemo hZ history ((2*v.val+1)+1) := by
  classical
  dsimp only
  apply markedMemoryStageBirthValues_memo
  · intro a
    rfl
  · intro a
    exact markedMemoryPotentialGhostValue_vertex_birth hZ history v a.1 a.2
  · intro a ht hn
    rcases a with ⟨j,k⟩ | ⟨w,j,k⟩ | ⟨w,j⟩
    · simp only [markedMemoryPotentialChronologicalTime] at ht
      omega
    · have hw : w=v := Fin.ext (by
        simp only [markedMemoryPotentialChronologicalTime] at ht
        omega)
      subst w
      have hk : ¬k.val < ((markedMemoryHistoryVertexGhost hZ history v).sizes.1 j:ℕ) := by
        intro hk
        apply hn
        exact markedMemoryStageDraw_mem _ (markedMemoryGhostStageDraw_injective v _)
          ⟨j,⟨k.val,hk⟩⟩
      exact markedMemoryPotentialGhostValue_vertex_absent hZ history v j k hk
    · simp only [markedMemoryPotentialChronologicalTime] at ht
      omega

end
end ArtinMatthews
