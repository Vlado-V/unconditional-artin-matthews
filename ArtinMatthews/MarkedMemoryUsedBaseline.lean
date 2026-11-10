module

public import ArtinMatthews.MarkedMemoryHistoryBirths
public import ArtinMatthews.MarkedMemoryIndependentHistory
public import ArtinMatthews.MarkedMemoryIndependentMarks
public import ArtinMatthews.MarkedMemoryInitialMeasure
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
public import Mathlib.Tactic.ENatToNat
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

/-! Extracting one baseline for every band prime cancels the baseline
denominator exactly once for each used prime. Numeric distinctness is
kept as the explicit global performed-birth condition. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

theorem markedMemory_baseline_used_cancel {I : Type*} [Fintype I]
    (S : Finset Nat.Primes) (p : I → Nat.Primes) (hinj : Function.Injective p)
    (hmem : ∀ i,p i∈S) (b : Nat.Primes → ℝ) (hb : ∀ s∈S,b s≠0) (c : I → ℝ) :
    (∏ s∈S,b s)*(∏ i,c i/b (p i)) =
      (∏ s∈S \ Finset.univ.image p,b s)*(∏ i,c i) := by
  have hsub : Finset.univ.image p⊆S := by
    intro s hs
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hs
    exact hmem i
  have hn : (∏ i,b (p i))≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hb (p i) (hmem i))
  rw [← Finset.prod_sdiff hsub]
  rw [Finset.prod_image (fun a _ c _ h => hinj h),Finset.prod_div_distrib]
  field_simp

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (order : Fin n → J → Equiv.Perm (Fin pads))

def markedMemoryUsedPrimes : Finset Nat.Primes := Finset.univ.image (markedMemoryIndependentPrime hZ d)

omit [∀ j,DecidableEq (A j)] in
theorem markedMemoryUsedPrimes_subset :
    markedMemoryUsedPrimes hZ d⊆Finset.univ.biUnion P := by
  intro p hp
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hp
  exact Finset.mem_biUnion.mpr ⟨a.1,Finset.mem_univ _,(d.particle a.1 a.2).1.2⟩

theorem markedMemoryIndependentPrime_injective_of_birthDistinct
    (hempty : ∀ j,(d.lifespan j).initial=[])
    (hd : MarkedMemoryHistoryBirthDistinct hZ (markedMemoryIndependentHistory hZ d order)) :
    Function.Injective (markedMemoryIndependentPrime hZ d) := by
  have hs : ∀ j,((markedMemoryIndependentState hZ d 0 (Nat.zero_le n)).2.2.1.1 j:ℕ)=0 := by
    intro j
    change ((markedMemoryIndependentMemory hZ d 0 (by omega)).1.1 j:ℕ)=0
    rw [markedMemory_initial_memory_empty hZ d hempty]
    rfl
  have hi := markedMemoryHistoryTraceAddressPrime_injective hZ
    (markedMemoryIndependentHistory hZ d order) hs hd
  let e := markedMemoryIndependentAddressEquiv hZ d order
  intro a b hab
  apply e.symm.injective
  apply hi
  have ha := markedMemoryIndependentAddress_prime hZ d order (e.symm a)
  have hb := markedMemoryIndependentAddress_prime hZ d order (e.symm b)
  rw [e.apply_symm_apply] at ha hb
  exact ha.symm.trans (hab.trans hb)

theorem markedMemory_used_baseline_cancel
    (hempty : ∀ j,(d.lifespan j).initial=[])
    (hd : MarkedMemoryHistoryBirthDistinct hZ (markedMemoryIndependentHistory hZ d order))
    (q : ℝ) (hb : ∀ p∈Finset.univ.biUnion P,markedMemoryBaseline q n p≠0)
    (c : (Σ j,A j) → ℝ) :
    (∏ p∈Finset.univ.biUnion P,markedMemoryBaseline q n p)*
        (∏ a : Σ j,A j,c a/markedMemoryBaseline q n (markedMemoryIndependentPrime hZ d a)) =
      (∏ p∈(Finset.univ.biUnion P) \ markedMemoryUsedPrimes hZ d,markedMemoryBaseline q n p)*
        ∏ a : Σ j,A j,c a :=
  markedMemory_baseline_used_cancel _ _
    (markedMemoryIndependentPrime_injective_of_birthDistinct hZ d order hempty hd)
    (fun a => Finset.mem_biUnion.mpr ⟨a.1,Finset.mem_univ _,(d.particle a.1 a.2).1.2⟩)
    (fun p => markedMemoryBaseline q n p) hb c

end
end ArtinMatthews
