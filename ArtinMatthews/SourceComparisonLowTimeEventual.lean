module

public import ArtinMatthews.SourceComparisonActualLowTime
public import ArtinMatthews.SourceComparisonActualDivisorBudget
public import ArtinMatthews.SourceComparisonLowTimeNumerics


set_option backward.privateInPublic true
@[expose] public section

/-! The literal comparison endpoint saves every fixed logarithmic power
throughout any fixed logarithmic Mellin window. -/
namespace ArtinMatthews
open Filter Finset MeasureTheory
open scoped BigOperators Topology
noncomputable section

universe u v
variable {J : Type u} [Fintype J]

theorem sourceComparisonCenteredMellinSum_lowTime_eventually (e : J → ℝ)
    (he : ∀ j, (1/10 : ℝ) < e j ∧ e j < 1/5) (heinj : Function.Injective e)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4)
    {a b₀ B : ℝ} (ha : 0 < a) (hab : a ≤ b₀) (hB : b₀ < B) (C S F A : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ {G : Type v} [Fintype G] (i : G ↪ GiantCandidateGroupIndex x)
      (t : G → ℕ), (∀ g, t g ≤ m) →
      ∀ (q : G → ℝ), (∀ g, 0 ≤ q g ∧ q g ≤ 1) →
      ∀ (b : ((g : G) → Fin (t g) → ℕ) → ℂ),
        (∀ l ∈ sourceComparisonMarkChoices (giantCandidateGroup x ∘ i) t, ‖b l‖ ≤ 1) →
      ∀ (Y σ τ : ℝ), x ^ (1 - ε/4) ≤ Y → Y ≤ x ^ (1 + ε/4) →
        |σ| ≤ (Real.log x) ^ S → |τ| ≤ (Real.log x) ^ S →
      ∀ ψ : ℝ → ℂ, ContDiff ℝ 1 ψ → (∀ z ∉ Set.Icc a b₀, ψ z = 0) →
        (∀ z, ‖ψ z‖ ≤ (Real.log x) ^ F) → (∀ z, ‖deriv ψ z‖ ≤ (Real.log x) ^ F) →
      ∀ (k : ℕ) [NeZero k], (k : ℝ) ≤ (Real.log x) ^ C → ∀ h : ℤ,
      ‖sourceComparisonCenteredMellinSum e ε x Y σ B ψ (giantCandidateGroup x ∘ i) t q b k h τ‖ ≤
        (Real.log x) ^ (-A) := by
  have hB₀ := (ha.trans_le hab).trans hB
  obtain ⟨D, E, K, hD, hE, hK, hbudget⟩ :=
    sourceComparisonActualDivisorBudget_eventually.{u,v} e he heinj m
      (by norm_num : (0:ℝ) < 1/2) (by norm_num) (2 * (A + F + 1))
  filter_upwards [sourceComparisonActualBands_geometry_eventually.{u,v} e he heinj,
    sourceComparisonActualBands_long_eventually.{u,v} e he heinj hε hεq C,
    sourceComparisonGiantCenter_eq_window_eventually B hB₀.le hεq.le,
    sourceComparisonLowTime_rounding_absorb_eventually hε hεq ha hB₀ C F S A,
    marked_sublinear_log_exp_le_rpow_eventually (47/100) K (ε/8) (by norm_num) (by positivity),
    hbudget, eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2 * B))]
    with x hG hLong hcap hround hxR hBudget hx hL hBL
  intro G _ i t ht q hq b hb Y σ τ hYlo hYhi hσ hτ ψ hψ hs h0 h1 k _ hk h
  let P := giantCandidateGroup x ∘ i
  let Q := sourceComparisonActualBands e x i
  let u : J ⊕ G → ℕ := Sum.elim (fun _ => 1) t
  let L := Real.log x
  let Z := Real.exp (L ^ (46/100:ℝ))
  let j := ⌊L ^ (1/100:ℝ)⌋₊
  let Λ := giantPrimeWindow x ε
  let N := (Λ.card : ℝ) + sourceComparisonLongReciprocal Λ
  let R := Real.exp (∑ p ∈ univ.biUnion Q, 1 / (p : ℝ)) * Z ^ ((∑ g, u g) + j)
  have hL₀ : 0 < L := zero_lt_one.trans_le hL
  have hM : 0 ≤ L ^ F := Real.rpow_nonneg hL₀.le _
  have hY : 0 < Y := (Real.rpow_pos_of_pos (zero_lt_one.trans hx) _).trans_le hYlo
  have hZ : 1 ≤ Z := Real.one_le_exp_iff.mpr (Real.rpow_nonneg hL₀.le _)
  have hR₀ : 0 ≤ R := mul_nonneg (Real.exp_pos _).le (pow_nonneg (zero_le_one.trans hZ) _)
  have hN₀ : 0 ≤ N := by unfold N sourceComparisonLongReciprocal; positivity
  obtain ⟨hd, hm, hp, _⟩ := hG i
  obtain ⟨hΛ, hsep, hcard, hCx, hcop⟩ := hLong i
  obtain ⟨_, _, _, hErr, hR⟩ := hBudget i t ht
  have hN : N ≤ x ^ (1 - ε/2) + 1 := add_le_add hcard hCx.2
  have hc (n : ℕ) (hn : n ∈ Ioc 0 ⌊B * Y⌋₊) :
      giantMarkedCenteredCore ε x n =
        (giantWindowDivisorCount Λ n - ∑ p ∈ Λ, 1 / (p : ℝ) : ℝ) := by
    obtain ⟨hn₀, hn₁⟩ := mem_Ioc.mp hn
    exact hcap Y hYhi n hn₀ ((Nat.cast_le.mpr hn₁).trans (Nat.floor_le (mul_nonneg hB₀.le hY.le)))
  have hlow := sourceComparisonCenteredMellinSum_bound e ε x Y σ B ψ P t q b hb k h τ j
    ha hab hB hY hψ hs hM hM h0 h1 hc hCx hq hΛ hZ hd (fun p h => (hp p h).1)
    (fun g => (by positivity : 0 < Real.log 2 / 2).trans (hm g).1)
    (fun p h => (hp p h).2.2) hsep (hcop k (Nat.pos_of_ne_zero (NeZero.ne k)) hk)
  have h₁ := sourceComparisonLowTime_truncation_absorb hL hB₀.le hBL hErr
  have h₂ := hround Y N R k σ τ hYlo hN₀ hN hR₀ (hR.trans hxR) (Nat.cast_nonneg _) hk hσ hτ
  exact hlow.trans ((add_le_add h₁ h₂).trans_eq (by ring))

end
end ArtinMatthews
