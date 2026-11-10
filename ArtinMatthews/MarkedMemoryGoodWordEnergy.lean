module

public import ArtinMatthews.MarkedMemoryHistoryChronological
public import ArtinMatthews.MarkedMinorArcDirtyScalar
public import ArtinMatthews.MarkedMinorArcDirtySecondGood
public import ArtinMatthews.MarkedMinorArcRawGhostActualRow
public import ArtinMatthews.MarkedMinorArcRawEdgeGoodEnergy
public import ArtinMatthews.MarkedMinorArcRawEdgeSymmetry
public import ArtinMatthews.MarkedMinorArcRawGhostEnergyBound
public import ArtinMatthews.MarkedMinorArcRawGhostSymmetry
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Energy of the literal forward chronological word, with the actual
first-good and beta-good cutoff at every edge. All ghost and edge estimates
are discharged by the actual arithmetic theorems. This is a statement in
the tilted memory space; it does not identify that space with the original
constant-mass physical endpoint space. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators

theorem markedMemoryChronologicalApply_symmetric
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (hχ : ∀ j z a, MarkedRawMemorySymmetric (fun m => χ j (z,(a,m))))
    (f : MarkedRawState P (pads+1) B Z → ℂ)
    (hf : ∀ z a, MarkedRawMemorySymmetric (fun m => f (z,(a,m))))
    (n j : ℕ) (z : Z) (a : MarkedRawActive P (pads+1)) :
    MarkedRawMemorySymmetric (fun m =>
      markedMemoryChronologicalApply ν V hZ ψ η d₀ Y Q ρ qStage χ n j f (z,(a,m))) := by
  induction n generalizing j z a with
  | zero => exact markedRawGhostApply_symmetric ν V (qStage j) ρ hZ f hf z a
  | succ n ih =>
    apply markedRawGhostApply_symmetric
    exact markedRawSlotAverage_symmetric _
      (markedRawEdgeApply_symmetric ν V hZ ψ η d₀ Y Q ρ (χ j) _ (hχ j)
        (markedRawSlotAverage_symmetric _ (ih (j+1))))

set_option backward.isDefEq.respectTransparency false in
theorem markedMemoryGoodChronological_actual_energy
    {J : Type*} [Fintype J] [decJ : DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10 : ℝ) ≤ e j) (hinj : Function.Injective e)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (hη : Function.support η ⊆ Set.Icc 1 4) (hηnorm : ∀ t, ‖η t‖ ≤ 1)
    (q ρ G H c T A W : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    (hρ : 0 < ρ) (hρ₁ : ρ < 1) (hgap : Real.sqrt q < ρ^2)
    (hG : 0 < G) (hH : 1 ≤ H) (hc : 0 < c)
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hW : 0 ≤ W)
    (hdepth : 100*(5*G+26) < (Fintype.card J : ℝ))
    (hψnorm : ∀ t, ‖ψ t‖ ≤ W) (hsupp : Function.support ψ ⊆ Set.Icc (-A) A) :
    ∀ᶠ x : ℝ in atTop, ∀ (Z : Finset (ℤ × ℤ))
      (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (r d₀ Y : ℝ) (w : Z → ℤ × ℤ)
      (χ : ℕ → MarkedRawState (markedRawActualPrimeBand e x)
        (markedPadSlots x) (markedDirtyMemoryCutoff x) Z → ℂ)
      (qStage : ℕ → ℝ)
      (f : MarkedRawState (markedRawActualPrimeBand e x)
        (markedPadSlots x) (markedDirtyMemoryCutoff x) Z → ℂ),
      0 < d₀ → Real.exp ((Real.log x)^(1/10 : ℝ)) ≤ Y →
      Y ≤ Real.exp (H*(Real.log x)^(1/5 : ℝ)) →
      (∀ z, markedMinorIntegerDet z.1 (w z) = 1) →
      (∀ z ∈ Z, c ≤ |markedMinorIntegerTau r z| ∧ |markedMinorIntegerTau r z| ≤ T) →
      (∀ z v : Z, |markedMinorIntegerTau r v.1/markedMinorIntegerTau r z.1| ≤ 16) →
      (∀ j s, ‖χ j s‖ ≤ 1) →
      (∀ j z a, MarkedRawMemorySymmetric (fun m => χ j (z,(a,m)))) →
      (∀ j, 0 ≤ qStage j ∧ qStage j ≤ Real.sqrt q) →
      (∀ z a, MarkedRawMemorySymmetric (fun m => f (z,(a,m)))) →
      ∀ n j : ℕ,
      let ν := markedRawActualPrimeAtom e q x
      let V := fun i => bandReciprocalMass (markedLogPowerBand (e i) x)
      let C := Real.exp ((Fintype.card J : ℝ)*(2*markedRawGhostSchurParameter q ρ/ρ))
      let ε := (Real.log x)^(-G)
      (∑ s, markedRawStateMass ν s *
        ‖markedMemoryChronologicalApply ν V hZ ψ η d₀ Y ((Real.log x)^(G+7)) ρ qStage
          (fun i => markedRawDirtyGoodCutoff e x r d₀ Y w (χ i)) n j f s‖^2) ≤
        (C^(n+1)*ε^n)^2 * ∑ s, markedRawStateMass ν s*‖f s‖^2 := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  filter_upwards [marked_minor_actual_raw_ghost_energy e he hq₀ hq₁ hρ hgap,
    markedRawEdge_good_actual_energy e he hinj ψ η hη hηnorm G H c T A W ρ
      hG hH hc hT hA hW hρ.le hρ₁ hdepth hψnorm hsupp] with x hghost hedge
  intro Z hZ r d₀ Y w χ qStage f hd₀ hYlo hYhi hw hτ hbox hχ hχsym hstage hf n j
  let ν := markedRawActualPrimeAtom e q x
  let V := fun i => bandReciprocalMass (markedLogPowerBand (e i) x)
  let C := Real.exp ((Fintype.card J : ℝ)*(2*markedRawGhostSchurParameter q ρ/ρ))
  let ε := (Real.log x)^(-G)
  let χg := fun i => markedRawDirtyGoodCutoff e x r d₀ Y w (χ i)
  let F := fun n j => markedMemoryChronologicalApply ν V hZ ψ η d₀ Y
    ((Real.log x)^(G+7)) ρ qStage χg n j f
  have hχg : ∀ i z a, MarkedRawMemorySymmetric (fun m => χg i (z,(a,m))) :=
    fun i => markedRawDirtyGoodCutoff_symmetric e x r d₀ Y w (χ i) (hχsym i)
  have hF : ∀ n j z a, MarkedRawMemorySymmetric (fun m => F n j (z,(a,m))) :=
    fun n j => markedMemoryChronologicalApply_symmetric ν V hZ ψ η d₀ Y
      ((Real.log x)^(G+7)) ρ qStage χg hχg f hf n j
  change (∑ s, markedRawStateMass ν s*‖F n j s‖^2) ≤
    (C^(n+1)*ε^n)^2 * ∑ s, markedRawStateMass ν s*‖f s‖^2
  induction n generalizing j with
  | zero =>
    simp only [F, markedMemoryChronologicalApply, Nat.zero_add,
      pow_one, pow_zero, mul_one]
    convert hghost (qStage j) (hstage j).1 (hstage j).2 _ _ Z hZ f hf using 1
    apply Finset.sum_congr (by ext s; simp only [Finset.mem_univ])
    intro s _
    rfl
  | succ n ih =>
    let E := markedRawEdgeSymmetrized ν V hZ ψ η d₀ Y ((Real.log x)^(G+7)) ρ (χg j) (F n (j+1))
    have hEsym : ∀ z a, MarkedRawMemorySymmetric (fun m => E (z,(a,m))) :=
      markedRawSlotAverage_symmetric _
        (markedRawEdgeApply_symmetric ν V hZ ψ η d₀ Y ((Real.log x)^(G+7)) ρ
          (χg j) _ (hχg j) (markedRawSlotAverage_symmetric _ (hF n (j+1))))
    have hg := hghost (qStage j) (hstage j).1 (hstage j).2 _ _ Z hZ E hEsym
    have he' := hedge Z hZ q r d₀ Y w (χ j) (F n (j+1)) hq₀ hq₁ hd₀ hYlo hYhi
      hw hτ hbox (hχ j) (hχsym j) (hF n (j+1))
    calc
      _ ≤ C^2 * ∑ s, markedRawStateMass ν s*‖E s‖^2 := hg
      _ ≤ C^2 * (ε^2 * ∑ s, markedRawStateMass ν s*‖F n (j+1) s‖^2) :=
        mul_le_mul_of_nonneg_left he' (sq_nonneg C)
      _ ≤ C^2 * (ε^2 * ((C^(n+1)*ε^n)^2 * ∑ s, markedRawStateMass ν s*‖f s‖^2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (ih (j+1)) (sq_nonneg ε)) (sq_nonneg C)
      _ = _ := by rw [pow_succ, pow_succ]; ring

end ArtinMatthews
