module

public import ArtinMatthews.GiantMarkedCharacterCriterion
public import ArtinMatthews.GiantOrdinaryProxyTuple
public import ArtinMatthews.GiantSlotCutoffError
public import ArtinMatthews.GiantSlotMellinActual
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

/-! Actual ordinary prime-slot replacement at the original normalized
tuple carrier. The proxy receives the same shifted cutoff and factorial. -/

namespace ArtinMatthews
noncomputable section
open Filter Finset
open scoped BigOperators Asymptotics ContDiff

theorem giant_ordinary_tuple_proxy_difference_isLittleO {J : Type}
    [Fintype J] [DecidableEq J] (e : J → ℝ) (hinj : Function.Injective e)
    (he : ∀ j,(1/10:ℝ) < e j ∧ e j < (1/5:ℝ))
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (Φ : ℝ → ℝ) {a T : ℝ} (ha : 0 < a) (hT : 0 < T)
    (hsupp : Function.support Φ ⊆ Set.Icc a T) (hΦ : ContDiff ℝ ∞ Φ)
    (γ : ℝ) (hγ : 0 < γ) {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4)
    (j : ℕ) (hj : 2 ≤ j)
    (hdepth : 100*(5*(29+2*(((j-1)*(j-1)+6:ℕ):ℝ))+36) < (Fintype.card J:ℝ)) :
    (fun x => giantOrdinaryTupleSum e χ (giantMarkedCenteredCore ε) Φ T γ j x -
      giantOrdinaryProxyTupleSum e χ (giantMarkedCenteredCore ε) Φ T γ j x)
      =o[atTop] (fun x : ℝ => x/Real.log x) := by
  let k := j-1
  let C := k*k+6
  let G := giantMarkedCenteredCore ε
  have hk : 0 < k := by dsimp only [k]; omega
  have hlen : k+1=j := Nat.sub_add_cancel (by omega)
  have hΦc : HasCompactSupport Φ := by
    change IsCompact (closure (Function.support Φ))
    exact isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal hsupp isClosed_Icc)
  have hG : ∀ᶠ x : ℝ in atTop,∀ n,‖G x n‖≤1 :=
    (giantMarkedCenteredCore_interface e (fun l => (he l).2.trans (by norm_num)) hε hεq).mono
      (fun _ h => h.1)
  have hslot (i : Fin (k+1)) :
      giantOrdinarySlotDiscrepancy e χ G Φ T γ i =o[atTop] (fun x : ℝ => x/Real.log x) := by
    have hc := giant_ordinary_slot_cutoff_error_isLittleO e
      (fun l => (by norm_num : (0:ℝ)<1/10).trans (he l).1) χ G hG Φ hΦ hΦc T γ hT.le hγ i
    have hu : giantOrdinarySlotUnshifted e χ G Φ T γ i =o[atTop] (fun x : ℝ => x/Real.log x) :=
      giant_unshifted_slot_isLittleO e hinj he χ Φ ha hT hsupp hΦ γ hγ C
        (by dsimp only [C]; omega) hε hεq hdepth
        (fun x => giantOrdinaryTruncatedCofactor i γ x)
        (giantOrdinaryTruncatedCofactor_bounds_eventually hk i γ hγ)
    apply (hc.add hu).congr' _ EventuallyEq.rfl
    filter_upwards [] with x
    exact sub_add_cancel _ _
  have hsum : (fun x => ∑ i : Fin (k+1),giantOrdinarySlotDiscrepancy e χ G Φ T γ i x)
      =o[atTop] (fun x : ℝ => x/Real.log x) := by
    apply (Asymptotics.IsLittleO.sum (s:=Finset.univ) (fun i _ => hslot i)).congr'
      _ EventuallyEq.rfl
    filter_upwards [] with x
    simp only [Finset.sum_apply]
  apply (hsum.const_mul_left (((k+1).factorial:ℂ)⁻¹)).congr' _ EventuallyEq.rfl
  filter_upwards [] with x
  change ((k+1).factorial:ℂ)⁻¹*(∑ i : Fin (k+1),giantOrdinarySlotDiscrepancy e χ G Φ T γ i x) =
    giantOrdinaryTupleSum e χ G Φ T γ j x-giantOrdinaryProxyTupleSum e χ G Φ T γ j x
  rw [← hlen,giant_ordinary_tuple_sub_proxy_eq_slots]
  rw [div_eq_mul_inv,mul_comm]

end
end ArtinMatthews
