module

public import ArtinMatthews.MarkedMinorArcDirtySecondError
public import ArtinMatthews.MarkedRawBoundaryActual
public import Mathlib.CategoryTheory.Countable


set_option backward.privateInPublic true
@[expose] public section

/-! Conditional bad-root measure for each literal active list. This is
a statement about the continuous root parameter, not an operator norm of
the corresponding projection on arbitrary raw states. -/
namespace ArtinMatthews
noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

def markedRawFirstBadRootSet {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M : ℕ} (a : MarkedRawActive P M) (d₀ Y : ℝ) :
    Set (AddCircle (1:ℝ)) :=
  markedFirstBadRoots
    (fun choice : markedRawDyadicOmissions a d₀ =>
      markedSourceCopiedProduct (markedRawNumericActive a) choice.1)
    ⌊Y^(1/5:ℝ)⌋₊ (Y^(-7/10:ℝ))

theorem markedRawFirstBadRootSet_measurable {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M : ℕ} (a : MarkedRawActive P M) (d₀ Y : ℝ) :
    MeasurableSet (markedRawFirstBadRootSet a d₀ Y) := by
  unfold markedRawFirstBadRootSet markedFirstBadRoots
  apply MeasurableSet.iUnion
  intro i
  apply Finset.measurableSet_biUnion
  intro l _
  exact measurableSet_markedBadRootMultiple _ _

theorem markedRawFirstBadRootSet_measure_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M : ℕ} (a : MarkedRawActive P M) (d₀ : ℝ)
    {Y : ℝ} (hY : 0 < Y) :
    volume.real (markedRawFirstBadRootSet a d₀ Y) ≤
      2*(M:ℝ)^(Fintype.card J)*Y^(-1/2:ℝ) := by
  have hpos (choice : markedRawDyadicOmissions a d₀) :
      0 < markedSourceCopiedProduct (markedRawNumericActive a) choice.1 := by
    exact Finset.prod_pos (fun j _ => Finset.prod_pos (fun k _ => (a j k).1.2.pos))
  have h := markedFirstBadRoots_parameter_bound
    (fun choice : markedRawDyadicOmissions a d₀ =>
      markedSourceCopiedProduct (markedRawNumericActive a) choice.1) hpos hY
  have hcard : (Fintype.card (markedRawDyadicOmissions a d₀):ℝ) ≤ (M:ℝ)^(Fintype.card J) := by
    have hnat : Fintype.card (markedRawDyadicOmissions a d₀) ≤ Fintype.card (J → Fin M) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    simp only [Fintype.card_fun,Fintype.card_fin] at hnat
    exact_mod_cast hnat
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcard (by norm_num)) (Real.rpow_nonneg hY.le _))

theorem markedPairFailureProbability_measurable {ι : Type*} [Fintype ι]
    (Q : Finset ℤ) (T : ι → ℤ) (w : ι → ℝ) (ε : ℝ) :
    Measurable (markedPairFailureProbability Q T w ε) := by
  unfold markedPairFailureProbability
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.indicator (measurableSet_markedPairBadRoots Q (T i) ε)

theorem markedRawDirtyBetaEvent_measurable {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ)
    (a : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
    (I : Finset J) (j : J) : MeasurableSet (markedRawDirtyBetaEvent e x a I j) := by
  exact measurableSet_le measurable_const (markedPairFailureProbability_measurable _ _ _ _)

theorem markedRawDirtyBetaBadRoots_measurable {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ)
    (a : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x)) :
    MeasurableSet (markedRawDirtyBetaBadRoots e x a) := by
  unfold markedRawDirtyBetaBadRoots
  apply MeasurableSet.iUnion
  intro p
  split_ifs
  · exact markedRawDirtyBetaEvent_measurable e x a p.1 p.2
  · exact MeasurableSet.empty

def markedRawBadRootSet {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x d₀ Y : ℝ)
    (a : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x)) : Set (AddCircle (1:ℝ)) :=
  markedRawFirstBadRootSet a d₀ Y ∪ markedRawDirtyBetaBadRoots e x a

theorem markedRawBadRootSet_measurable {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x d₀ Y : ℝ)
    (a : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x)) :
    MeasurableSet (markedRawBadRootSet e x d₀ Y a) :=
  (markedRawFirstBadRootSet_measurable a d₀ Y).union (markedRawDirtyBetaBadRoots_measurable e x a)

theorem markedRawBadRootSet_log_saving {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (hinj : Function.Injective e) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop,∀ d₀ Y : ℝ,
      Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y →
      ∀ a : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x),
        volume.real (markedRawBadRootSet e x d₀ Y a) ≤ (Real.log x)^(-A) := by
  let K := Fintype.card J
  have hfirst := marked_polynomial_exp_eventually_le ((2:ℝ)^(K+1)) ((K:ℝ)/100) A
    (by norm_num : (0:ℝ)<1/10) (by norm_num : (0:ℝ)<1/2) (by norm_num : (0:ℝ)<1/2)
  have hsecond := marked_polynomial_exp_eventually_le (200*(2:ℝ)^K*(K:ℝ)) 0 A
    (by norm_num : (0:ℝ)<1/10) (by norm_num : (0:ℝ)<1/2) (by norm_num : (0:ℝ)<1/2)
  filter_upwards [markedRawDirtyBetaBadRoots_measure_eventually e he hinj,
    Real.tendsto_log_atTop.eventually hfirst,Real.tendsto_log_atTop.eventually hsecond,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hb hf hs hlog
  intro d₀ Y hY a
  have hYpos : 0 < Y := (Real.exp_pos _).trans_le hY
  have hpow : Y^(-1/2:ℝ) ≤ Real.exp (-(1/2:ℝ)*(Real.log x)^(1/10:ℝ)) := by
    convert marked_length_negative_rpow_le
      (c := 1) (τ := (1/2:ℝ)) (by norm_num) (by simpa only [one_mul] using hY) using 1 <;> norm_num
  have hp := markedPadSlots_pow_le K hlog
  have hfm : volume.real (markedRawFirstBadRootSet a d₀ Y) ≤
      (1/2:ℝ)*(Real.log x)^(-A) := by
    apply (markedRawFirstBadRootSet_measure_le a d₀ hYpos).trans
    calc
      _ ≤ 2*((2:ℝ)^K*(Real.log x)^((K:ℝ)/100))*
          Real.exp (-(1/2:ℝ)*(Real.log x)^(1/10:ℝ)) := by gcongr
      _ = (2:ℝ)^(K+1)*(Real.log x)^((K:ℝ)/100)*
          Real.exp (-(1/2:ℝ)*(Real.log x)^(1/10:ℝ)) := by rw [pow_succ]; ring
      _ ≤ _ := hf
  have hsm : volume.real (markedRawDirtyBetaBadRoots e x a) ≤
      (1/2:ℝ)*(Real.log x)^(-A) :=
    (hb a).trans (by simpa only [Real.rpow_zero,mul_one] using hs)
  exact (measureReal_union_le _ _).trans ((add_le_add hfm hsm).trans_eq (by ring))

end
end ArtinMatthews
