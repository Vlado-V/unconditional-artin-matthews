module

public import ArtinMatthews.MarkedBirthRankCutoff
public import ArtinMatthews.MarkedMemoryBirthEventBoundary
public import ArtinMatthews.MarkedBirthLowRankBudget
public import ArtinMatthews.MarkedBirthMixedBudget
public import ArtinMatthews.MarkedBirthRankSums
public import ArtinMatthews.MarkedMemoryBirthEventActual
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

/-! The actual low-rank part of the original performed-birth expansion.
Every event is the true oriented chronological sum. The depth condition
uses exactly the existing two-power whole-word margin. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

local instance lowRankPotentialPermFintype {J : Type*} [Fintype J] [DecidableEq J] (M B N : ℕ) :
    Fintype (Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) :=
  @Equiv.instFintype (MarkedMemoryPotentialAddress J M B N)
    (MarkedMemoryPotentialAddress J M B N) inferInstance inferInstance inferInstance inferInstance

set_option backward.isDefEq.respectTransparency false in
theorem markedMemoryBirth_low_rank_actual
    {J : Type*} [Fintype J] [decJ : DecidableEq J]
    (e : J → ℝ) (he : ∀ i, (1/10:ℝ) ≤ e i) (hinj : Function.Injective e)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (hη : Function.support η ⊆ Set.Icc 1 4) (hηnorm : ∀ u, ‖η u‖ ≤ 1)
    (q ρ G H c T A W cutoffScale : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    (hρ : 0 < ρ) (hρ₁ : ρ < 1) (hgap : Real.sqrt q < ρ^2)
    (hG : 0 < G) (hH : 1 ≤ H) (hc : 0 < c) (hT : 0 ≤ T) (hA : 0 ≤ A) (hW : 0 ≤ W)
    (hScale : 0 ≤ cutoffScale) (hdepth : 100*(5*G+36) < (Fintype.card J:ℝ))
    (hψ : ∀ u, ‖ψ u‖ ≤ W) (hsupp : Function.support ψ ⊆ Set.Icc (-A) A) :
    ∀ᶠ x : ℝ in atTop, ∀ (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
      (r d₀ Y : ℝ) (w : Z → ℤ × ℤ) (z₀ : Z) (orientation : ℕ → Bool),
      0 < d₀ → Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y → Y ≤ Real.exp (H*(Real.log x)^(1/5:ℝ)) →
      (∀ z, markedMinorIntegerDet z.1 (w z) = 1) →
      (∀ z ∈ Z, c ≤ |markedMinorIntegerTau r z| ∧ |markedMinorIntegerTau r z| ≤ T) →
      (∀ z v : Z, |markedMinorIntegerTau r v.1/markedMinorIntegerTau r z.1| ≤ 16) →
      let N := markedMemoryMomentLength x
      (∑ σ : Equiv.Perm (MarkedMemoryPotentialAddress J (markedPadSlots x) (markedDirtyMemoryCutoff x) N),
        if markedBirthPermutationRank σ < markedBirthRankCutoff cutoffScale x then
          ‖markedMemoryBirthEventBoundaryPairing (pads := ⌊(Real.log x)^(1/100:ℝ)⌋₊)
            (markedRawActualPrimeAtom e q x) (fun i => bandReciprocalMass (markedLogPowerBand (e i) x))
            hZ ψ η d₀ Y ((Real.log x)^(G+9)) ρ orientation (markedMemoryWordVisitQ q N)
            (fun _ => markedRawDirtyGoodCutoff e x r d₀ Y w (fun _ => 1)) σ z₀‖ else 0) ≤
        ((Real.log x)^(-(G+1)))^N := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  let v₀ := markedRawGhostSchurParameter q ρ
  let C := Real.exp ((Fintype.card J:ℝ)*(2*v₀/ρ))
  let P := 2*(Fintype.card J:ℝ)+3*(G+9)+1
  have hv₀ : 1 ≤ v₀ := markedRawGhostSchurParameter_ge_one q ρ
  have hC : 1 ≤ C := by
    apply Real.one_le_exp_iff.mpr
    positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hdepth' : 100*(5*(G+2)+26) < (Fintype.card J:ℝ) := by linarith
  have hevent := markedMemoryBirthEventBoundary_actual_bound e he hinj ψ η hη hηnorm q ρ (G+2) H c T A W
    hq₀ hq₁ hρ hρ₁ hgap (by linarith) hH hc hT hA hW hdepth' hψ hsupp
  have hp := markedBirthCrudeEdgeBudget_polynomial (Fintype.card J) v₀ W A (G+2) hv₀ hW hA
  have hQ : G+2+7 = G+9 := by ring
  simp only [hQ] at hevent hp
  filter_upwards [hevent,hp,markedBirth_low_rank_budget (Fintype.card J) C P G cutoffScale hC hP hG hScale,
    markedBirthRankCutoff_le_fraction hScale (by norm_num : (0:ℝ)<1/2),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
    with x hEvent hRpoly hbudget hcut hlog
  intro Z hZ r d₀ Y w z₀ orientation hd₀ hYlo hYhi hw hτ hbox
  let N := markedMemoryMomentLength x
  let L := Real.log x
  let r₀ := markedBirthRankCutoff cutoffScale x
  let ε := L^(-(G+2))
  let R := markedRawEdgeCrudeActualConstant (Fintype.card J) v₀ 1 W A 1 *
    (markedDirtyMemoryCutoff x+1:ℝ)^(Fintype.card J)*(L^(G+9))^3
  let F := fun σ : Equiv.Perm (MarkedMemoryPotentialAddress J (markedPadSlots x) (markedDirtyMemoryCutoff x) N) =>
    ‖markedMemoryBirthEventBoundaryPairing (markedRawActualPrimeAtom e q x)
      (fun i => bandReciprocalMass (markedLogPowerBand (e i) x)) hZ ψ η d₀ Y (L^(G+9)) ρ orientation
      (markedMemoryWordVisitQ q N) (fun _ => markedRawDirtyGoodCutoff e x r d₀ Y w (fun _ => 1)) σ z₀‖
  let E := fun k : ℕ => 2*C^(N+1)*ε^(N-2*k)*(L^P)^(2*k)
  have hL₁ : 1 ≤ L := hlog
  have hL : 0 < L := zero_lt_one.trans_le hL₁
  have hε₀ : 0 ≤ ε := Real.rpow_nonneg hL.le _
  have hε₁ : ε ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL₁ (by linarith)
  have hR₀ : 0 ≤ R := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hv₀₀ := zero_le_one.trans hv₀
    dsimp [R,markedRawEdgeCrudeActualConstant]
    positivity
  have hR : max 1 R ≤ L^P := max_le (Real.one_le_rpow hL₁ hP) hRpoly
  have hE (k : ℕ) : 0 ≤ E k := by dsimp [E]; positivity
  have hbound (σ) (hσ : markedBirthPermutationRank σ < r₀) : F σ ≤ E (markedBirthPermutationRank σ) := by
    let k := markedBirthPermutationRank σ
    let m := markedOperatorModifiedEdgeCount (MarkedMemoryBirthEdgeModified σ) N 0
    have hmk : m ≤ 2*k := markedMemoryBirth_modified_edges_le_twice_rank σ
    have hkN : 2*k ≤ N := by
      have hk : (k:ℝ) ≤ (r₀:ℝ) := by exact_mod_cast (Nat.le_of_lt hσ)
      have hc' : (r₀:ℝ) ≤ (1/2:ℝ)*(N:ℝ) := hcut
      exact_mod_cast (show 2*(k:ℝ) ≤ (N:ℝ) by linarith)
    have hm := markedMixedEdgeBudget_mono_count hε₀ hε₁ hR₀ hmk hkN
    have he' := hEvent Z hZ r d₀ Y w z₀ N σ orientation hd₀ hYlo hYhi hw hτ hbox
    change F σ ≤ 2*C^(N+1)*ε^(N-m)*R^m at he'
    calc
      F σ ≤ 2*C^(N+1)*(ε^(N-2*k)*(max 1 R)^(2*k)) :=
        he'.trans (by
          simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_left hm (show 0 ≤ 2*C^(N+1) by positivity))
      _ ≤ E k := by
        change 2*C^(N+1)*(ε^(N-2*k)*(max 1 R)^(2*k)) ≤
          2*C^(N+1)*ε^(N-2*k)*(L^P)^(2*k)
        rw [mul_assoc (2*C^(N+1))]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hR (2*k))
            (pow_nonneg hε₀ _)) (by positivity)
  have hsum := markedBirthRank_low_sum_le r₀ F E (fun k _ => hE k) hbound
  rw [markedMemoryPotentialAddress_actual_card] at hsum
  apply hsum.trans
  simpa only [E,N,L,r₀,mul_assoc] using hbudget

end ArtinMatthews
