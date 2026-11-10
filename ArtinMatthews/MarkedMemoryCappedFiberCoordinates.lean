module

public import ArtinMatthews.MarkedMemoryActualCappedPrerequisites
public import ArtinMatthews.MarkedMemoryCappedPathAssembly
public import ArtinMatthews.MarkedMemoryIndependentPathChoices
public import ArtinMatthews.MarkedMemoryCappedPathNormalizedIndex
public import ArtinMatthews.MarkedMemoryCappedPathRecovery
public import ArtinMatthews.MarkedMemoryFiniteTableauInjective
public import ArtinMatthews.MarkedMemoryPrimePathFiniteRecovery
public import ArtinMatthews.MarkedMemoryPrimePathRelabel
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

/-! Every member of a capped history fiber has the same prime-valued
path, optional endpoints and copied orders, recovered from the actual
history. Label equivalences come from the proved full-tableau fiber. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (hP : ∀ i j,i≠j → Disjoint (P i) (P j))
  (s : MarkedRawState P (pads+1) B Z) (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)
  (H : MarkedMemoryPrimeSupportedHistory (n := n) hZ s)
  (i : MarkedMemoryCappedPathDecoratedIndex (n := n) hZ s)
  (hi : markedMemoryCappedPathDecoratedAssembly hZ hP s i=H.1)

include hP hi in
theorem markedMemoryCappedFiber_coordinates :
    i.1.path=markedMemoryIndependentActivePath hZ (markedMemoryActualTableau hZ H.1 H.2.1)
        (markedMemoryActualCapped_prime_injective hZ H.1 H.2.1 hempty H.2.2.1) ∧
      i.1.choices=markedMemoryIndependentPathChoices hZ (markedMemoryActualTableau hZ H.1 H.2.1) ∧
      i.2.2=markedMemoryActualOrder hZ H.1 H.2.1 := by
  let base := markedMemoryActualTableau hZ H.1 H.2.1
  let hb := markedMemoryActualCapped_prime_injective hZ H.1 H.2.1 hempty H.2.2.1
  let raw := markedMemoryCappedPathIndependent (B := B) hZ i.1.path i.1.choices i.1.compatible i.1.capacity i.2.1
  let hr := markedMemoryCappedPathIndependent_prime_injective (B := B) hZ i.1.path i.1.choices i.1.compatible i.1.capacity i.2.1 hP
  obtain ⟨rename,hf,ho⟩ := markedMemoryCappedPathFiber_extraction hZ hP s i hempty H.1 H.2.1 hi
  let renamed := markedMemoryIndependentRelabel hZ rename base
  let hren := markedMemoryIndependentPrime_relabel_injective hZ rename base hb
  have hf' : markedMemoryIndependent_toFinite hZ renamed=markedMemoryIndependent_toFinite hZ raw :=
    hf.trans (markedMemoryFiniteTableau_restrict_extend hZ
      (markedMemoryCappedPathTableau (B := B) hZ i.1.path i.1.choices i.1.compatible i.1.capacity i.2.1)).symm
  have hp := markedMemoryIndependentActivePath_finite_eq hZ renamed hren raw hr hf'
  have hc := markedMemoryIndependentPathChoices_finite_eq hZ renamed raw hf'
  have hp0 := markedMemoryIndependentActivePath_relabel hZ rename base hb
  have hc0 := markedMemoryIndependentPathChoices_relabel hZ rename base hb
  have hp1 := markedMemoryCappedPathIndependent_path (B := B) hZ i.1.path i.1.choices i.1.compatible i.1.capacity i.2.1 hP
  have hc1 := markedMemoryCappedPathIndependent_choices (B := B) hZ i.1.path i.1.choices i.1.compatible i.1.capacity i.2.1 hP
  exact ⟨(hp0.symm.trans (hp.trans hp1)).symm,(hc0.symm.trans (hc.trans hc1)).symm,ho.symm⟩

end
end ArtinMatthews
