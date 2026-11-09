module

public import ArtinMatthews.MarkedMemoryBirthEventCrude
public import ArtinMatthews.MarkedBirthHighRankPrefactor
public import ArtinMatthews.MarkedBirthMixedBudget
public import ArtinMatthews.MarkedMemoryGoodWordActual


set_option backward.privateInPublic true
@[expose] public section

/-! The actual high-rank prefactor is polynomial per operation. This
includes the genuine initial active tuples, every ghost and the full
crude edge constant, with B=ceil(log(x)^2) and the original moment length. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedMemoryBirthEventCrudeExponent (K : ℕ) (G : ℝ) : ℝ :=
  2*(K:ℝ)+3*(G+9)+3

set_option backward.isDefEq.respectTransparency false in
theorem markedMemoryBirthEventBoundary_actual_polynomial
    {J : Type*} [Fintype J] [decJ : DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (hη : ∀ u,‖η u‖ ≤ 1)
    (q ρ G W A : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hgap : Real.sqrt q < ρ^2)
    (hG : 0 < G) (hW : 0 ≤ W) (hA : 0 ≤ A)
    (hψ : ∀ u,‖ψ u‖ ≤ W) (hsupp : Function.support ψ ⊆ Set.Icc (-A) A) :
    ∀ᶠ x : ℝ in atTop, ∀ (Z : Finset (ℤ × ℤ))
      (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (r d₀ Y : ℝ) (w : Z → ℤ × ℤ) (z₀ : Z)
      (orientation : ℕ → Bool)
      (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (markedPadSlots x)
        (markedDirtyMemoryCutoff x) (markedMemoryMomentLength x))),
      Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y →
      (∀ z,markedMinorIntegerDet z.1 (w z)=1) →
      (∀ z : Z,markedMinorIntegerTau r z.1≠0) →
      (∀ z v : Z,|markedMinorIntegerTau r v.1/markedMinorIntegerTau r z.1| ≤ 16) →
      ‖markedMemoryBirthEventBoundaryPairing (pads := ⌊(Real.log x)^(1/100:ℝ)⌋₊)
        (markedRawActualPrimeAtom e q x) (fun i => bandReciprocalMass (markedLogPowerBand (e i) x))
        hZ ψ η d₀ Y ((Real.log x)^(G+9)) ρ orientation
        (markedMemoryWordVisitQ q (markedMemoryMomentLength x))
        (fun _ => markedRawDirtyGoodCutoff e x r d₀ Y w (fun _ => 1)) σ z₀‖ ≤
      ((Real.log x)^(markedMemoryBirthEventCrudeExponent (Fintype.card J) G))^(markedMemoryMomentLength x+1)*
        (markedMemoryBirthAtomEnvelope x)^(markedBirthPermutationRank σ) := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  let v₀ := markedRawGhostSchurParameter q ρ
  let Cg := Real.exp ((Fintype.card J:ℝ)*(2*v₀/ρ))
  let P := 2*(Fintype.card J:ℝ)+3*(G+9)+1
  have hv₀ : 1 ≤ v₀ := markedRawGhostSchurParameter_ge_one q ρ
  have hCg : 1 ≤ Cg := by apply Real.one_le_exp_iff.mpr; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hpoly := markedBirthCrudeEdgeBudget_polynomial (Fintype.card J) v₀ W A (G+2) hv₀ hW hA
  have hQeq : G+2+7=G+9 := by ring
  simp only [hQeq] at hpoly
  filter_upwards [markedMemoryBirthEventBoundary_actual_atom_bound e he hq₀ hq₁ hρ hρ₁ hgap,
    hpoly,markedBirth_high_rank_prefactor_budget (Fintype.card J) Cg P hCg hP,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
    with x hb hRpoly hpref hlog
  intro Z hZ r d₀ Y w z₀ orientation σ hYlo hw hτ hbox
  let R := markedRawEdgeCrudeActualConstant (Fintype.card J) v₀ 1 W A 1*
    (markedDirtyMemoryCutoff x+1:ℝ)^(Fintype.card J)*((Real.log x)^(G+9))^3
  have hR : 0 ≤ R := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [R,markedRawEdgeCrudeActualConstant]
    positivity
  have hY : 1 ≤ Y := (Real.one_le_exp (Real.rpow_nonneg (zero_le_one.trans hlog) _)).trans hYlo
  have hQ : 1 ≤ (Real.log x)^(G+9) := Real.one_le_rpow hlog (by linarith)
  have hχ : ∀ (j : ℕ) (s : MarkedRawState (markedRawActualPrimeBand e x)
      (markedPadSlots x) (markedDirtyMemoryCutoff x) Z),
      ‖(fun _ => markedRawDirtyGoodCutoff e x r d₀ Y w (fun _ => 1)) j s‖ ≤ 1 := by
    intro _ s
    exact markedRawDirtyGoodCutoff_norm_le e x r d₀ Y w (fun _ => 1) (by intro; simp) s
  have hevent := hb ⌊(Real.log x)^(1/100:ℝ)⌋₊ (markedDirtyMemoryCutoff x) (markedMemoryMomentLength x)
    Z hZ ψ η r d₀ Y ((Real.log x)^(G+9)) 1 W A w σ z₀ orientation
    (markedMemoryWordVisitQ q (markedMemoryMomentLength x))
    (fun _ => markedRawDirtyGoodCutoff e x r d₀ Y w (fun _ => 1))
    hY hQ zero_le_one hW hA hη hψ (fun u hu => abs_le.mpr (hsupp hu)) hw hτ hbox
    (markedMemoryWordVisitQ_bounds hq₀ hq₁ _) hχ
  apply hevent.trans
  have hp := mul_le_mul_of_nonneg_right (hpref R hR hRpoly)
    (pow_nonneg (markedMemoryBirthAtomEnvelope_pos x).le (markedBirthPermutationRank σ))
  have hPeq : P+2=markedMemoryBirthEventCrudeExponent (Fintype.card J) G := by
    dsimp [P,markedMemoryBirthEventCrudeExponent]
    ring
  simpa only [R,Cg,v₀,hPeq,markedPadSlots] using hp

end ArtinMatthews
