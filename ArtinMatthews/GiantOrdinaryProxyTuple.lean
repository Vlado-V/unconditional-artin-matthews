module

public import ArtinMatthews.GiantMixedSlotCofactor
public import ArtinMatthews.GiantPrimeExtractionArithmetic
public import ArtinMatthews.GiantSlotBilinearReindex
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The original ordinary tuple and its rough proxy share the same
ordered carrier, shift, character, and factorial. The signed difference
is the sum of the literal slot discrepancies. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

theorem giant_prime_factor_fiber_eq {q : ℕ} (χ : DirichletCharacter ℂ q)
    (k n : ℕ) (z : ℝ) :
    (∑ t ∈ giantOrderedProductFiber k n,∏ i,χ (t i)*giantPrimeSlotCoefficient z (t i)) =
      roughPrimeTupleCoefficient (fun p => χ p) k n z := by
  classical
  let S := giantOrderedProductFiber k n
  let E := S.filter (fun t => ∀ i,(t i).Prime ∧ z < (t i:ℝ))
  calc
    _ = ∑ t ∈ E,∏ i,χ (t i)*giantPrimeSlotCoefficient z (t i) := by
      symm
      apply sum_subset (filter_subset _ _)
      intro t ht hn
      have hbad : ¬ ∀ i,(t i).Prime ∧ z < (t i:ℝ) := fun h => hn (mem_filter.mpr ⟨ht,h⟩)
      obtain ⟨i,hi⟩ := not_forall.mp hbad
      have hz : giantPrimeSlotCoefficient z (t i)=0 := by
        by_cases hzi : z < (t i:ℝ)
        · have hp : ¬(t i).Prime := fun h => hi ⟨h,hzi⟩
          simp only [giantPrimeSlotCoefficient,hzi,hp,ite_true,ite_false]
        · exact ite_eq_right hzi
      apply prod_eq_zero (mem_univ i)
      rw [hz,mul_zero]
    _ = ∑ t ∈ E,∏ i,χ (t i) := by
      apply sum_congr rfl
      intro t ht
      apply prod_congr rfl
      intro i _
      obtain ⟨hp,hz⟩ := (mem_filter.mp ht).2 i
      simp only [giantPrimeSlotCoefficient,hp,hz,ite_true,mul_one]
    _ = _ := by
      unfold roughPrimeTupleCoefficient
      apply sum_bij (fun t _ => List.ofFn t)
      · intro t ht
        obtain ⟨ht₁,ht₂⟩ := mem_filter.mp ht
        apply (mem_roughOrderedPrimeFactorizations _ _ _ _).mpr
        exact ⟨List.length_ofFn,
          List.prod_ofFn.trans (mem_giantOrderedProductFiber.mp ht₁).2,
          List.forall_mem_ofFn_iff.mpr ht₂⟩
      · intro t _ u _ h
        exact List.ofFn_injective h
      · intro l hl
        obtain ⟨hlen,hprod,hp⟩ := (mem_roughOrderedPrimeFactorizations _ _ _ _).mp hl
        subst k
        let t : Fin l.length → ℕ := l.get
        have ht (i : Fin l.length) : (t i).Prime ∧ z < (t i:ℝ) :=
          hp _ (List.get_mem l i)
        have hprod' : (∏ i,t i)=n := by
          rw [← List.prod_ofFn]
          exact (congrArg List.prod (List.ofFn_get l)).trans hprod
        exact ⟨t,mem_filter.mpr ⟨mem_giantOrderedProductFiber.mpr
          ⟨fun i => (ht i).1.pos,hprod'⟩,ht⟩,List.ofFn_get l⟩
      · intro t _
        rw [List.map_ofFn,List.prod_ofFn]
        rfl

theorem giantOrdinaryTupleSum_eq_ordered {J : Type*} [Fintype J]
    (e : J → ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℝ → ℕ → ℂ)
    (Φ : ℝ → ℝ) (T γ x : ℝ) (k : ℕ) :
    giantOrdinaryTupleSum e χ G Φ T γ k x =
      (∑ t ∈ giantOrderedProductTuples k ⌊T*x⌋₊,
        markedExtractionWeight e G Φ x (∏ i,t i) *
          ∏ i,χ (t i)*giantPrimeSlotCoefficient (x^γ) (t i)) / k.factorial := by
  let X := ⌊T*x⌋₊
  let z := x^γ
  let w := markedExtractionWeight e G Φ x
  let S := giantOrderedProductTuples k X
  let g (t : Fin k → ℕ) := ∏ i,t i
  let F (t : Fin k → ℕ) := w (g t)*∏ i,χ (t i)*giantPrimeSlotCoefficient z (t i)
  unfold giantOrdinaryTupleSum
  simp_rw [← mul_div_assoc,← sum_div]
  apply congrArg (fun y : ℂ => y / k.factorial)
  change (∑ n ∈ Ioc 0 X,w n * roughPrimeTupleCoefficient (fun p => χ p) k n z) = ∑ t ∈ S,F t
  have hg : ∀ t ∈ S,g t ∈ Ioc 0 X := by
    intro t ht
    obtain ⟨ht₀,htX⟩ := mem_giantOrderedProductTuples.mp ht
    exact mem_Ioc.mpr ⟨prod_pos (fun i _ => ht₀ i),htX⟩
  calc
    _ = ∑ n ∈ Ioc 0 X,∑ t ∈ S.filter (fun t => g t=n), F t := by
      apply sum_congr rfl
      intro n hn
      have he : S.filter (fun t => g t=n) = giantOrderedProductFiber k n :=
        giantOrderedProductFiber_filter (mem_Ioc.mp hn).2
      rw [he,← giant_prime_factor_fiber_eq χ k n z,mul_sum]
      apply sum_congr rfl
      intro t ht
      dsimp only [F,g]
      rw [(mem_giantOrderedProductFiber.mp ht).2]
    _ = _ := sum_fiberwise_of_maps_to hg F

def giantOrdinaryProxyTupleSum {J : Type*} [Fintype J]
    (e : J → ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℝ → ℕ → ℂ)
    (Φ : ℝ → ℝ) (T γ : ℝ) (k : ℕ) (x : ℝ) : ℂ :=
  (∑ t ∈ giantOrderedProductTuples k ⌊T*x⌋₊, markedExtractionWeight e G Φ x (∏ i,t i) *
    ∏ i,χ (t i)*giantRoughSlotCoefficient (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) (t i)) / k.factorial

def giantOrdinarySlotDiscrepancy {J : Type*} [Fintype J]
    (e : J → ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℝ → ℕ → ℂ)
    (Φ : ℝ → ℝ) (T γ : ℝ) {k : ℕ} (i : Fin (k+1)) (x : ℝ) : ℂ :=
  let X := ⌊T*x⌋₊
  let W := Real.exp ((Real.log x)^(6/25:ℝ))
  let z := x^γ
  ∑ mn ∈ ((Ioc 0 X)×ˢ(Ioc 0 X)).filter (fun mn => mn.1*mn.2 ≤ X),
    markedExtractionWeight e G Φ x (mn.1*mn.2) * χ (mn.1*mn.2) *
      (if z < (mn.1:ℝ) then markedMajorCenteredCoefficient W 0 mn.1 else 0) *
      giantMixedCofactorCoefficient i W z mn.2

theorem giant_ordinary_tuple_sub_proxy_eq_slots {J : Type*} [Fintype J]
    (e : J → ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℝ → ℕ → ℂ)
    (Φ : ℝ → ℝ) (T γ x : ℝ) (k : ℕ) :
    giantOrdinaryTupleSum e χ G Φ T γ (k+1) x - giantOrdinaryProxyTupleSum e χ G Φ T γ (k+1) x =
      (∑ i : Fin (k+1),giantOrdinarySlotDiscrepancy e χ G Φ T γ i x) / (k+1).factorial := by
  rw [giantOrdinaryTupleSum_eq_ordered,giantOrdinaryProxyTupleSum,← sub_div]
  apply congrArg (fun y : ℂ => y/(k+1).factorial)
  rw [giant_fixed_character_weighted_slots_telescope]
  apply sum_congr rfl
  intro i _
  exact giant_slot_discrepancy_eq_bilinear χ ⌊T*x⌋₊
    (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) i (markedExtractionWeight e G Φ x)

end
end ArtinMatthews
