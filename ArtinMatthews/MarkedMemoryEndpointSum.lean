module

public import ArtinMatthews.MarkedMemoryEndpointFactors
public import ArtinMatthews.MarkedMemoryActualBoundedHistory
public import ArtinMatthews.MarkedMemoryDecorationAverage
public import ArtinMatthews.MarkedMemoryNormalizedFiberSum
public import ArtinMatthews.MarkedMemoryDecorationAlgebra
public import ArtinMatthews.MarkedMemoryEndpointDecorations
public import ArtinMatthews.MarkedMemoryNormalizedEndpointSum
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

/-! The actual signed history sum as a bare endpoint-family sum. Birth
factorials cancel their proved global enumeration fibers; copied orders
leave their exact slot mass. Arbitrary guards and tests remain evaluated
on the actual decorated history inside its finite average. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
  {A : J → Type*} [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]

def markedMemoryEndpointSlotMass : ℂ :=
  (markedMemoryCopiedOrderCount J pads n : ℂ) *
    ((Fintype.card (MarkedMemorySlotPermutations J (pads+1)) : ℂ)⁻¹)^(2*n)

theorem markedMemorySlotPower_identity (a b : ℂ) (k : ℕ) :
    a^k*(b⁻¹)^(2*k)=(a/b^2)^k := by
  have hp : (b^2)^k=b^(2*k) := (pow_mul b 2 k).symm
  rw [div_pow,hp]
  simp only [div_eq_mul_inv,inv_pow]

theorem markedMemoryEndpointSlotMass_eq :
    markedMemoryEndpointSlotMass (J := J) (pads := pads) (n := n) =
      (((pads.factorial : ℂ)^Fintype.card J) /
        ((((pads+1).factorial : ℂ)^Fintype.card J)^2))^n := by
  unfold markedMemoryEndpointSlotMass markedMemoryCopiedOrderCount
  simp only [Fintype.card_fun,Fintype.card_perm,Fintype.card_fin,Nat.cast_pow]
  exact markedMemorySlotPower_identity _ _ n

def markedMemoryEndpointKernel
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (keep : MarkedMemoryChronologicalHistory hZ n s → Prop)
    (f : MarkedRawState P (pads+1) B Z → ℂ)
    (e : MarkedMemoryEndpointFamily (A := A) (n := n) hZ s)
    (births : MarkedMemoryEndpointBirthOrders e.1)
    (order : Fin n → J → Equiv.Perm (Fin pads)) : ℂ :=
  let i := markedMemoryEndpointFamilyIndex hZ s e births order
  let H := markedMemoryNormalizedHistoryAssembly hZ s i
  if keep H then
    markedMemoryHistoryRawEdgeProduct hZ ψ η d₀ Y Q χ n 0
      (markedMemoryIndependentHistory hZ (markedMemoryEndpointIndependent hZ s e births) order) *
        f (markedMemoryChronologicalTarget hZ H)
  else 0

theorem markedMemoryEndpointDecoration_term
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q q : ℝ) (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (keep : MarkedMemoryChronologicalHistory hZ n s → Prop)
    (f : MarkedRawState P (pads+1) B Z → ℂ)
    (e : MarkedMemoryEndpointFamily (A := A) (n := n) hZ s) (L : ℂ)
    (births : MarkedMemoryEndpointBirthOrders e.1) (order : Fin n → J → Equiv.Perm (Fin pads)) :
    (let i := markedMemoryEndpointFamilyIndex hZ s e births order
     let H := markedMemoryNormalizedHistoryAssembly hZ s i
     if keep H then markedMemoryNormalizedEndpointWeight hZ s ν V ψ η d₀ Y Q q χ i *
       f (markedMemoryChronologicalTarget hZ H) / L else 0) =
    ((markedMemoryEndpointPrimeScalar hZ s e ν V q : ℂ)/(markedMemoryEndpointBirthFactorial e.1 : ℂ)) *
      (((Fintype.card (MarkedMemorySlotPermutations J (pads+1)) : ℂ)⁻¹)^(2*n)) *
      markedMemoryEndpointKernel hZ s ψ η d₀ Y Q χ keep f e births order / L := by
  dsimp only
  rw [markedMemoryEndpointWeight_factor]
  unfold markedMemoryEndpointKernel
  dsimp only
  split_ifs <;> push_cast <;> ring

theorem markedMemoryEndpointDecoration_weighted_sum
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q q : ℝ) (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (keep : MarkedMemoryChronologicalHistory hZ n s → Prop)
    (f : MarkedRawState P (pads+1) B Z → ℂ)
    (e : MarkedMemoryEndpointFamily (A := A) (n := n) hZ s) (L : ℂ) :
    (∑ births : MarkedMemoryEndpointBirthOrders e.1,
      ∑ order : Fin n → J → Equiv.Perm (Fin pads),
        let i := markedMemoryEndpointFamilyIndex hZ s e births order
        let H := markedMemoryNormalizedHistoryAssembly hZ s i
        if keep H then markedMemoryNormalizedEndpointWeight hZ s ν V ψ η d₀ Y Q q χ i *
          f (markedMemoryChronologicalTarget hZ H) / L else 0) =
    (markedMemoryEndpointPrimeScalar hZ s e ν V q : ℂ) *
      markedMemoryEndpointSlotMass (J := J) (pads := pads) (n := n) *
      markedMemoryDecorationAverage e.1 (markedMemoryEndpointKernel hZ s ψ η d₀ Y Q χ keep f e) / L := by
  calc
    _ = ∑ births : MarkedMemoryEndpointBirthOrders e.1,
        ∑ order : Fin n → J → Equiv.Perm (Fin pads),
        ((markedMemoryEndpointPrimeScalar hZ s e ν V q : ℂ)/(markedMemoryEndpointBirthFactorial e.1 : ℂ)) *
          (((Fintype.card (MarkedMemorySlotPermutations J (pads+1)) : ℂ)⁻¹)^(2*n)) *
          markedMemoryEndpointKernel hZ s ψ η d₀ Y Q χ keep f e births order / L := by
      apply Finset.sum_congr rfl
      intro births _
      exact Finset.sum_congr rfl (fun order _ =>
        markedMemoryEndpointDecoration_term hZ s ν V ψ η d₀ Y Q q χ keep f e L births order)
    _ = _ := by
      unfold markedMemoryEndpointSlotMass
      exact markedMemoryDecoration_weighted_average_instances (J := J) (A := A) (P := P) (pads := pads) (n := n) (Z := Z)
        e.1 (inferInstance : Fintype (MarkedMemoryEndpointBirthOrders e.1))
        (inferInstance : Fintype (MarkedMemoryCopiedOrders (J := J) (pads := pads) (n := n)))
        (markedMemoryEndpointPrimeScalar hZ s e ν V q : ℂ)
        (((Fintype.card (MarkedMemorySlotPermutations J (pads+1)) : ℂ)⁻¹)^(2*n)) L
        (markedMemoryEndpointKernel hZ s ψ η d₀ Y Q χ keep f e)


local notation "K" => markedMemoryActualLabelBound (J := J) (pads := pads) (B := B) (n := n)

theorem markedMemoryEndpoint_signed_sum
    (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q q : ℝ) (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (keep : MarkedMemoryChronologicalHistory hZ n s → Prop)
    (f : MarkedRawState P (pads+1) B Z → ℂ) :
    (∑ H : MarkedMemoryChronologicalHistory hZ n s,
      if keep H then markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q 1
        (markedMemoryHistoryVisitSchedule q n) χ n 0 H * f (markedMemoryChronologicalTarget hZ H) else 0) =
    ∑ N : J → Fin (K+1),
      ∑ e : MarkedMemoryEndpointFamily (A := fun j => Fin (N j : ℕ)) (n := n) hZ s,
        (markedMemoryEndpointPrimeScalar hZ s e ν V q : ℂ) *
          markedMemoryEndpointSlotMass (J := J) (pads := pads) (n := n) *
          markedMemoryDecorationAverage e.1 (markedMemoryEndpointKernel hZ s ψ η d₀ Y Q χ keep f e) /
            (markedMemoryLabelFactorial (fun j => (N j:ℕ)) : ℂ) := by
  refine (markedMemoryNormalized_endpoint_guarded_sum hZ s hempty ν V ψ η d₀ Y Q q χ keep f).symm.trans ?_
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro N _
  let T : MarkedMemoryNormalizedHistoryIndex (A := fun j => Fin (N j : ℕ)) (n := n) hZ s → ℂ :=
    fun i => if keep (markedMemoryNormalizedHistoryAssembly hZ s i) then
      markedMemoryNormalizedEndpointWeight hZ s ν V ψ η d₀ Y Q q χ i *
        f (markedMemoryChronologicalTarget hZ (markedMemoryNormalizedHistoryAssembly hZ s i)) /
          (markedMemoryLabelFactorial (fun j => (N j : ℕ)) : ℂ) else 0
  change (∑ i,T i)=_
  refine (markedMemoryEndpointDecorations_sum hZ s hempty T).trans ?_
  apply Finset.sum_congr rfl
  intro e _
  exact markedMemoryEndpointDecoration_weighted_sum hZ s ν V ψ η d₀ Y Q q χ keep f e _


end
end ArtinMatthews
