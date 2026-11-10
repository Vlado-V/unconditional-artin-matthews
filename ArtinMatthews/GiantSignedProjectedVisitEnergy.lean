module

public import ArtinMatthews.GiantSignedProjectedWord
public import ArtinMatthews.GiantSignedSourceVisitEnergy
public import ArtinMatthews.GiantSignedCappedStateBound
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

/-! The original projected visits preserve pending symmetry and the
source polynomial energy bound on all symmetric tests. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

theorem giantSignedProjectedVisit_memorySymmetric
    {S B : Type*} [Fintype S] [Fintype B] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {M : ℕ}
    [Fintype (GiantTwoSidedResidueState PS M)] [∀ g, ∀ p : PB g, NeZero p.val]
    (N : ℕ) (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (V : B → ℝ) (q ρ : ℝ) (f : GiantSignedState PS PB M → ℂ)
    (hf : ∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m))) :
    ∀ s a, GiantSignedMemorySymmetric (fun m => giantSignedProjectedVisit N ν V q ρ f (s,a,m)) := by
  unfold giantSignedProjectedVisit
  apply giantSignedStateMemoryCutoff_memory_symmetric
  obtain ⟨U, hU, hb⟩ := giantSignedStateMemoryCutoff_bound N f
  exact giantSignedStateGhostApply_memorySymmetric PS ν hν
    (fun _ => ((q / ρ ^ 2 : ℝ) : ℂ)) (fun g => ((-(1-q) * V g / ρ : ℝ) : ℂ))
    (fun _ => ((-(1-q) / ρ : ℝ) : ℂ)) (giantSignedStateMemoryCutoff N f)
    (giantSignedStateMemoryCutoff_memory_symmetric N f hf) U 1 hU zero_lt_one
    (fun s a m => by simpa only [one_pow, mul_one] using hb (s,a,m))

theorem giantSignedProjectedVisitEnergy_exists {q ρ C₀ Vmax : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hgap : Real.sqrt q < ρ ^ 2)
    (hVmax : 0 ≤ Vmax) :
    ∃ v : ℝ, 1 < v ∧
      ∀ (S B : Type*) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
        (PS : S → Finset ℕ) (PB : B → Finset ℕ)
        [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
        [∀ g, ∀ p : PB g, NeZero p.val]
        (M N : ℕ) (ν : ∀ g, PB g → ℝ),
        (∀ g p, 0 ≤ ν g p) → (∀ g, (∑ p : PB g, ν g p) ≤ 2) →
      ∀ (V : B → ℝ), (∀ g, 0 ≤ V g) → (∀ g, V g ≤ Vmax) →
        (∀ g, 0 < bandReciprocalMass (PS g)) →
      ∀ (n : ℕ) (i : Fin (n+1)) (L : ℝ),
        0 < L → (Fintype.card B : ℝ) ≤ C₀ * Real.log L →
      ∀ (f : GiantSignedState PS PB M → ℂ),
        (∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m))) →
        giantSignedStateEnergy PS ν
          (giantSignedProjectedVisit N ν V (giantSignedSourceVisitQ q n i) ρ f) ≤
            ENNReal.ofReal (L ^ giantSignedSourceVisitExponent C₀ Vmax ρ v) *
              giantSignedStateEnergy PS ν f := by
  obtain ⟨v, hv, henergy⟩ := giantSignedSourceVisitEnergy_exists (C₀ := C₀) hq0 hq1 hρ hgap hVmax
  refine ⟨v, hv, ?_⟩
  intro S B _ _ _ _ PS PB _ _ M N ν hν hMass V hV0 hV hVS n i L hL hgroups f hsym
  classical
  obtain ⟨U, hU, hb⟩ := giantSignedStateMemoryCutoff_bound N f
  let w := giantSignedStateMemoryCutoff N f
  have hw : ∀ s a m, ‖w (s,a,m)‖ ≤ U * (1 : ℝ) ^ (∑ g, m.1 g) :=
    fun s a m => by simpa only [one_pow, mul_one] using hb (s,a,m)
  have h := henergy S B PS PB M ν hν hMass V hV0 hV hVS n i L hL hgroups w
    (giantSignedStateMemoryCutoff_memory_symmetric N f hsym) U 1 hU zero_lt_one hw
  refine (giantSignedStateMemoryCutoff_energy_le ν N
    (giantSignedChronologicalVisit ν V (giantSignedSourceVisitQ q n i) ρ w)).trans (h.trans ?_)
  exact mul_le_mul_right (giantSignedStateMemoryCutoff_energy_le ν N f) _

end
end ArtinMatthews
