module

public import ArtinMatthews.MarkedMemoryHistoryGhostChoice
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

/-! Reverse ghost coordinates use the old identities which continue and
an ordered list of new labels. Deletion masks and bounded dependent birth
sizes are reconstructed, rather than included in these coordinates. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {M B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P M B Z)

structure MarkedMemoryGhostRunData where
  retained : (j : J) → Finset (Fin (s.2.2.1.1 j : ℕ))
  born : (j : J) → List (↥(P j))
  deaths_hit : ∀ j, Finset.univ \ retained j ⊆ markedRawGroupHitIndices s.2.2 j s.1.1 (hZ _ s.1.2)
  memory_bound : (∑ j, ((retained j).card + (born j).length)) ≤ B

def markedMemoryGhostRunDeletion (d : MarkedMemoryGhostRunData hZ s) :
    MarkedRawGhostDeletion s.2.2 := fun j => Finset.univ \ d.retained j

theorem markedMemoryGhostRun_survivors (d : MarkedMemoryGhostRunData hZ s) (j : J) :
    markedRawGhostSurvivors s.2.2 (markedMemoryGhostRunDeletion hZ s d) j = d.retained j := by
  simp only [markedRawGhostSurvivors, markedMemoryGhostRunDeletion,
    Finset.sdiff_sdiff_self_left, Finset.univ_inter]

def markedMemoryGhostRunBirthSizes (d : MarkedMemoryGhostRunData hZ s) :
    MarkedRawGhostBirthSizes s.2.2 (markedMemoryGhostRunDeletion hZ s d) :=
  ⟨fun j => ⟨(d.born j).length, by
    have hj := (Finset.single_le_sum (fun i _ => Nat.zero_le
      ((d.retained i).card + (d.born i).length)) (Finset.mem_univ j)).trans d.memory_bound
    omega⟩, by simpa only [markedMemoryGhostRun_survivors] using d.memory_bound⟩

def markedMemoryGhostRunReconstruct (d : MarkedMemoryGhostRunData hZ s) : MarkedMemoryGhostChoice hZ s where
  deletion := markedMemoryGhostRunDeletion hZ s d
  allowed := d.deaths_hit
  sizes := markedMemoryGhostRunBirthSizes hZ s d
  births := fun j => (d.born j).get

def markedMemoryGhostRunEncode (c : MarkedMemoryGhostChoice hZ s) : MarkedMemoryGhostRunData hZ s where
  retained := markedRawGhostSurvivors s.2.2 c.deletion
  born := fun j => List.ofFn (c.births j)
  deaths_hit := by
    intro j
    simpa only [markedRawGhostSurvivors, Finset.sdiff_sdiff_self_left, Finset.univ_inter] using c.allowed j
  memory_bound := by simpa only [List.length_ofFn] using c.sizes.2

@[ext] theorem MarkedMemoryGhostRunData.ext {a b : MarkedMemoryGhostRunData hZ s}
    (hr : a.retained = b.retained) (hb : a.born = b.born) : a = b := by
  cases a
  cases b
  cases hr
  cases hb
  rfl

theorem markedMemoryGhostRun_encode_reconstruct (d : MarkedMemoryGhostRunData hZ s) :
    markedMemoryGhostRunEncode hZ s (markedMemoryGhostRunReconstruct hZ s d) = d := by
  apply MarkedMemoryGhostRunData.ext
  · funext j
    exact markedMemoryGhostRun_survivors hZ s d j
  · funext j
    exact List.ofFn_get (d.born j)

/-- The retained identities and the complete ordered new-label lists
determine all the literal ghost-choice fields uniquely. -/
theorem markedMemoryGhostRunEncode_injective : Function.Injective (markedMemoryGhostRunEncode hZ s) := by
  rintro ⟨da,ha,la,ba⟩ ⟨db,hb,lb,bb⟩ heq
  have hr := congrArg MarkedMemoryGhostRunData.retained heq
  have hd : da = db := by
    funext j
    have hj := congrFun hr j
    have hc := congrArg (fun S => Finset.univ \ S) hj
    simpa only [markedMemoryGhostRunEncode, markedRawGhostSurvivors,
      Finset.sdiff_sdiff_self_left, Finset.univ_inter] using hc
  cases hd
  have hlists := congrArg MarkedMemoryGhostRunData.born heq
  have hl : la = lb := by
    apply Subtype.ext
    funext j
    apply Fin.ext
    have hj := congrArg List.length (congrFun hlists j)
    simpa only [markedMemoryGhostRunEncode, List.length_ofFn] using hj
  cases hl
  have hbirths : ba = bb := by
    funext j
    apply List.ofFn_injective
    exact congrFun hlists j
  cases hbirths
  rfl

theorem markedMemoryGhostRun_reconstruct_encode (c : MarkedMemoryGhostChoice hZ s) :
    markedMemoryGhostRunReconstruct hZ s (markedMemoryGhostRunEncode hZ s c) = c := by
  apply markedMemoryGhostRunEncode_injective hZ s
  exact markedMemoryGhostRun_encode_reconstruct hZ s (markedMemoryGhostRunEncode hZ s c)

/-- A proved local inverse, with every ordered birth multiplicity kept. -/
def markedMemoryGhostRunEquiv : MarkedMemoryGhostChoice hZ s ≃ MarkedMemoryGhostRunData hZ s where
  toFun := markedMemoryGhostRunEncode hZ s
  invFun := markedMemoryGhostRunReconstruct hZ s
  left_inv := markedMemoryGhostRun_reconstruct_encode hZ s
  right_inv := markedMemoryGhostRun_encode_reconstruct hZ s

end
end ArtinMatthews
