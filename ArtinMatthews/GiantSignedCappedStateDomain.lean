module

public import ArtinMatthews.GiantSignedWordDomain
public import ArtinMatthews.GiantSignedStateMemoryCutoff
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

/-! Capping total degree gives finite support inside the original full
state. The cutoff of an arbitrary test is therefore exponentially bounded. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

abbrev GiantSignedCappedState {S B : Type*} [Fintype S] [Fintype B]
    (PS : S → Finset ℕ) (PB : B → Finset ℕ) (M N : ℕ) :=
  {s : GiantSignedState PS PB M // (∑ g, s.2.2.1 g) ≤ N}

variable {S B : Type*} [Fintype S] [Fintype B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {M : ℕ}
    [Fintype (GiantTwoSidedResidueState PS M)]
    [∀ g, ∀ p : PB g, NeZero p.val]

theorem giantSignedCappedState_finite (N : ℕ) :
    Finite (GiantSignedCappedState PS PB M N) := by
  classical
  let X := GiantTwoSidedResidueState PS M × (MarkedPhysicalMarking PB M ×
    (Σ d : B → Fin (N+1), ∀ g, Fin (d g).val → GiantSignedParticle (PB g)))
  let : Fintype X := by dsimp [X]; infer_instance
  have hd (s : GiantSignedCappedState PS PB M N) (g : B) : s.1.2.2.1 g < N+1 :=
    Nat.lt_succ_of_le ((Finset.single_le_sum (f := s.1.2.2.1)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)).trans s.2)
  let encode (s : GiantSignedCappedState PS PB M N) : X :=
    (s.1.1, s.1.2.1, ⟨fun g => ⟨s.1.2.2.1 g, hd s g⟩, s.1.2.2.2⟩)
  let decode (x : X) : GiantSignedState PS PB M :=
    (x.1, x.2.1, ⟨fun g => (x.2.2.1 g).val, x.2.2.2⟩)
  refine Finite.of_injective encode ?_
  intro s t h
  apply Subtype.ext
  exact congrArg decode h

theorem giantSignedStateMemoryCutoff_exponential (N : ℕ)
    (f : GiantSignedState PS PB M → ℂ) :
    GiantSignedWordExponential (giantSignedStateMemoryCutoff N f) := by
  classical
  let : Finite (GiantSignedCappedState PS PB M N) := giantSignedCappedState_finite N
  let := Fintype.ofFinite (GiantSignedCappedState PS PB M N)
  let C := ∑ s : GiantSignedCappedState PS PB M N, ‖f s.1‖
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  refine ⟨C, 1, hC, zero_lt_one, ?_⟩
  intro s
  rw [one_pow, mul_one]
  by_cases hs : (∑ g, s.2.2.1 g) ≤ N
  · rw [giantSignedStateMemoryCutoff_of_le N f s hs]
    exact Finset.single_le_sum (f := fun t : GiantSignedCappedState PS PB M N => ‖f t.1‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ ⟨s, hs⟩)
  · rw [giantSignedStateMemoryCutoff_of_lt N f s (lt_of_not_ge hs), norm_zero]
    exact hC

end
end ArtinMatthews
