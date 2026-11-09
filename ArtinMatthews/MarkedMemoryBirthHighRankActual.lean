module

public import ArtinMatthews.MarkedMemoryBirthEventPolynomial
public import ArtinMatthews.MarkedBirthHighRankSumBudget
public import ArtinMatthews.MarkedBirthRankHighSums


set_option backward.privateInPublic true
@[expose] public section

/-! The actual high-rank part of the original event expansion. All
conditional prime costs and the complete physical word prefactor have
been discharged before the finite rank sum is estimated. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

local instance highRankPotentialPermFintype {J : Type*} [Fintype J] [DecidableEq J] (M B N : ℕ) :
    Fintype (Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) :=
  @Equiv.instFintype (MarkedMemoryPotentialAddress J M B N)
    (MarkedMemoryPotentialAddress J M B N) inferInstance inferInstance inferInstance inferInstance

set_option backward.isDefEq.respectTransparency false in
theorem markedMemoryBirth_high_rank_actual
    {J : Type*} [Fintype J] [decJ : DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (hη : ∀ u,‖η u‖ ≤ 1)
    (q ρ G W A cutoffScale : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hgap : Real.sqrt q < ρ^2)
    (hG : 0 < G) (hW : 0 ≤ W) (hA : 0 ≤ A)
    (hψ : ∀ u,‖ψ u‖ ≤ W) (hsupp : Function.support ψ ⊆ Set.Icc (-A) A)
    (hScale : 2*(2*markedMemoryBirthEventCrudeExponent (Fintype.card J) G+G+2) ≤ cutoffScale) :
    ∀ᶠ x : ℝ in atTop, ∀ (Z : Finset (ℤ × ℤ))
      (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (r d₀ Y : ℝ) (w : Z → ℤ × ℤ) (z₀ : Z)
      (orientation : ℕ → Bool),
      Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y →
      (∀ z,markedMinorIntegerDet z.1 (w z)=1) →
      (∀ z : Z,markedMinorIntegerTau r z.1≠0) →
      (∀ z v : Z,|markedMinorIntegerTau r v.1/markedMinorIntegerTau r z.1| ≤ 16) →
      let N := markedMemoryMomentLength x
      (∑ σ : Equiv.Perm (MarkedMemoryPotentialAddress J (markedPadSlots x) (markedDirtyMemoryCutoff x) N),
        if markedBirthRankCutoff cutoffScale x ≤ markedBirthPermutationRank σ then
          ‖markedMemoryBirthEventBoundaryPairing (pads := ⌊(Real.log x)^(1/100:ℝ)⌋₊)
            (markedRawActualPrimeAtom e q x) (fun i => bandReciprocalMass (markedLogPowerBand (e i) x))
            hZ ψ η d₀ Y ((Real.log x)^(G+9)) ρ orientation (markedMemoryWordVisitQ q N)
            (fun _ => markedRawDirtyGoodCutoff e x r d₀ Y w (fun _ => 1)) σ z₀‖ else 0) ≤
        ((Real.log x)^(-(G+1)))^N := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  let P := markedMemoryBirthEventCrudeExponent (Fintype.card J) G
  have hP : 0 ≤ P := by dsimp [P,markedMemoryBirthEventCrudeExponent]; positivity
  filter_upwards [markedMemoryBirthEventBoundary_actual_polynomial e he ψ η hη q ρ G W A
    hq₀ hq₁ hρ hρ₁ hgap hG hW hA hψ hsupp,
    markedBirth_high_rank_sum_budget (Fintype.card J) P G cutoffScale hP hScale,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx hnum hlog
  intro Z hZ r d₀ Y w z₀ orientation hY hw hτ hbox
  let N := markedMemoryMomentLength x
  let C := ((Real.log x)^P)^(N+1)
  let F := fun σ : Equiv.Perm (MarkedMemoryPotentialAddress J (markedPadSlots x) (markedDirtyMemoryCutoff x) N) =>
    ‖markedMemoryBirthEventBoundaryPairing (pads := ⌊(Real.log x)^(1/100:ℝ)⌋₊)
      (markedRawActualPrimeAtom e q x) (fun i => bandReciprocalMass (markedLogPowerBand (e i) x))
      hZ ψ η d₀ Y ((Real.log x)^(G+9)) ρ orientation (markedMemoryWordVisitQ q N)
      (fun _ => markedRawDirtyGoodCutoff e x r d₀ Y w (fun _ => 1)) σ z₀‖
  have hC : 0 ≤ C := pow_nonneg (Real.rpow_nonneg (zero_le_one.trans hlog) _) _
  have hF (σ) : F σ ≤ C*(markedMemoryBirthAtomEnvelope x)^(markedBirthPermutationRank σ) :=
    hx Z hZ r d₀ Y w z₀ orientation σ hY hw hτ hbox
  have hs := markedBirthRank_high_sum_le (markedBirthRankCutoff cutoffScale x) F hC
    (markedMemoryBirthAtomEnvelope_pos x).le (fun σ _ => hF σ)
  rw [markedMemoryPotentialAddress_actual_card] at hs
  apply hs.trans
  simpa only [C,N,P] using hnum

end ArtinMatthews
