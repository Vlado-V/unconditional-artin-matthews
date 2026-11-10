module

public import ArtinMatthews.MarkedPhysicalCoordinateRootPolynomial
public import ArtinMatthews.MarkedPhysicalIndexBonferroni
public import ArtinMatthews.MarkedPhysicalIndexWeightChangeModulus
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact reindexing of the original guarded physical polynomial into
its selected-modulus root sums. Every selected subset uses its actual
modulus, while canonical integer coordinates remain unchanged. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J]
  (e : J → ℝ) (x : ℝ) (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
  (d₀ Y Q : ℝ) {R : ℕ}
  (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
    (markedPadSlots x) (markedMemoryMomentLength x) R) (hR : 1 ≤ R)

theorem markedPhysicalIndexMonomial_selected_root_sum (q U Vr : ℝ)
    (hU : 1 < U) (hVr : 1 < Vr) (T : Finset ℕ)
    (hT : T ⊆ markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x)) :
    let S := markedPhysicalBonferroniModulus Finset.univ i.1 T
    let _ : NeZero S := ⟨(markedPhysicalBonferroniModulus_pos
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) Finset.univ i.1 hT).ne'⟩
    markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
      V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i *
      (∑ r : MarkedPhysicalCanonicalRoot S U (16*U) Vr (2*Vr),
        markedPhysicalIndexMonomialWeight e x d₀ Y U Vr i hR q T r)=
      if markedPhysicalCoordinateIndexPath i.2.1 (Fin.last (markedMemoryMomentLength x))=(1,0) then
        markedPhysicalCoordinateSelectedRoot e x V ψ η d₀ Y Q i hR q U Vr T else 0 := by
  let C := markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
    V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i
  let : NeZero (markedPhysicalBonferroniModulus Finset.univ i.1 T) :=
    ⟨(markedPhysicalBonferroniModulus_pos
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) Finset.univ i.1 hT).ne'⟩
  dsimp only
  change C * (∑ r : MarkedPhysicalCanonicalRoot
      (markedPhysicalBonferroniModulus Finset.univ i.1 T) U (16*U) Vr (2*Vr),
      markedPhysicalIndexMonomialWeight e x d₀ Y U Vr i hR q T r) = _
  rw [Fintype.sum_sigma,Finset.mul_sum]
  have hp (g) (r : ↥(fixedURootMatrixBoxPoints g U (16*U) 0 1 Vr (2*Vr) true true true true true true)) :=
    markedPhysicalIndexMonomialWeight_selected e x d₀ Y U Vr i hR hU hVr q T hT ⟨g,r⟩
  by_cases hl : markedPhysicalCoordinateIndexPath i.2.1 (Fin.last (markedMemoryMomentLength x))=(1,0)
  · simp only [hl,ite_true,markedPhysicalCoordinateSelectedRoot,dite_eq_left hT]
    change (∑ g : Matrix.SpecialLinearGroup (Fin 2)
        (ZMod (markedPhysicalBonferroniModulus Finset.univ i.1 T)),
        C * ∑ r : ↥(fixedURootMatrixBoxPoints g U (16*U) 0 1 Vr (2*Vr) true true true true true true),
          markedPhysicalIndexMonomialWeight e x d₀ Y U Vr i hR q T ⟨g,r⟩) =
      ∑ g : Matrix.SpecialLinearGroup (Fin 2)
        (ZMod (markedPhysicalBonferroniModulus Finset.univ i.1 T)),
        markedRootConstantIndicatorSum g U Vr (markedPhysicalCoordinateIndexGoodSet e x d₀ Y U Vr i hR)
          ((markedPhysicalCoordinateIndexResidueFactor
            (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) i hR q T hT g:ℂ)*C)
    apply Finset.sum_congr rfl
    intro g _
    simp_rw [hp]
    simp only [hl,ite_true]
    rw [Finset.mul_sum]
    let F : (Σ _u : ℤ,ℤ × ℤ) → ℂ := fun r => C *
      (if markedRootNormalizedPoint U Vr r∈markedPhysicalCoordinateIndexGoodSet e x d₀ Y U Vr i hR then
        (markedPhysicalCoordinateIndexResidueFactor
          (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) i hR q T hT g:ℂ) else 0)
    change (∑ r : ↥(fixedURootMatrixBoxPoints g U (16*U) 0 1 Vr (2*Vr) true true true true true true),F r.1) = _
    rw [Finset.sum_coe_sort (fixedURootMatrixBoxPoints g U (16*U) 0 1 Vr (2*Vr) true true true true true true) F]
    dsimp only [F]
    unfold markedRootConstantIndicatorSum
    apply Finset.sum_congr rfl
    intro r _
    split_ifs <;> ring
  · simp only [hl,ite_false]
    apply Finset.sum_eq_zero
    intro g _
    simp_rw [hp]
    simp only [hl,ite_false,Finset.sum_const_zero,mul_zero]

theorem markedPhysicalIndexMonomial_fixed_root_sum (q U Vr : ℝ)
    (hU : 1 < U) (hVr : 1 < Vr) (S : ℕ) [NeZero S] (T : Finset ℕ)
    (hT : T ⊆ markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x)) :
    markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
      V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i *
      (∑ r : MarkedPhysicalCanonicalRoot S U (16*U) Vr (2*Vr),
        markedPhysicalIndexMonomialWeight e x d₀ Y U Vr i hR q T r)=
      if markedPhysicalCoordinateIndexPath i.2.1 (Fin.last (markedMemoryMomentLength x))=(1,0) then
        markedPhysicalCoordinateSelectedRoot e x V ψ η d₀ Y Q i hR q U Vr T else 0 := by
  let S' := markedPhysicalBonferroniModulus Finset.univ i.1 T
  let : NeZero S' := ⟨(markedPhysicalBonferroniModulus_pos
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) Finset.univ i.1 hT).ne'⟩
  rw [markedPhysicalIndexMonomialWeight_sum_changeModulus e x d₀ Y U Vr i hR q T S S' hU hVr]
  exact markedPhysicalIndexMonomial_selected_root_sum e x V ψ η d₀ Y Q i hR q U Vr hU hVr T hT

theorem markedPhysicalIndexPolynomial_fixed_root_sum (q U Vr : ℝ)
    (hU : 1 < U) (hVr : 1 < Vr) (S : ℕ) [NeZero S] (k : ℕ) :
    markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
      V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i *
      (∑ r : MarkedPhysicalCanonicalRoot S U (16*U) Vr (2*Vr),
        markedPhysicalIndexPolynomialWeight e x d₀ Y U Vr i hR q k r)=
      markedPhysicalCoordinateRootPolynomial e x V ψ η d₀ Y Q i hR q U Vr k := by
  let C := markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
    V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i
  let E := markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x) \
    markedPhysicalPathUsedPrimes Finset.univ i.1
  change C * (∑ r : MarkedPhysicalCanonicalRoot S U (16*U) Vr (2*Vr),
    markedPhysicalIndexPolynomialWeight e x d₀ Y U Vr i hR q k r) = _
  calc
    _ = ∑ j ∈ Finset.range (k+1),(-1:ℂ)^j * ∑ T ∈ E.powersetCard j,
        C * ∑ r : MarkedPhysicalCanonicalRoot S U (16*U) Vr (2*Vr),
          markedPhysicalIndexMonomialWeight e x d₀ Y U Vr i hR q T r := by
      simp_rw [markedPhysicalIndexPolynomialWeight_monomials]
      rw [Finset.sum_comm,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro T _
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = ∑ j ∈ Finset.range (k+1),(-1:ℂ)^j * ∑ T ∈ E.powersetCard j,
        (if markedPhysicalCoordinateIndexPath i.2.1 (Fin.last (markedMemoryMomentLength x))=(1,0) then
          markedPhysicalCoordinateSelectedRoot e x V ψ η d₀ Y Q i hR q U Vr T else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      apply Finset.sum_congr rfl
      intro T hT
      exact markedPhysicalIndexMonomial_fixed_root_sum e x V ψ η d₀ Y Q i hR q U Vr hU hVr S T
        (fun p hp => (Finset.mem_sdiff.mp ((Finset.mem_powersetCard.mp hT).1 hp)).1)
    _ = _ := by
      unfold markedPhysicalCoordinateRootPolynomial
      split_ifs <;> simp [E]

end
end ArtinMatthews
