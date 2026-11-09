module

public import ArtinMatthews.MarkedMemoryBirthPhaseWordEnergy
public import ArtinMatthews.MarkedMemoryModifiedEdgeCount
public import ArtinMatthews.MarkedWeightedBoundaryTwoSided
public import ArtinMatthews.MarkedMemoryGoodWordActual


set_option backward.privateInPublic true
@[expose] public section

/-! The true empty-memory boundary with its initial birth phases. The
right endpoint is the original boundary and the ν interior payload is one.
No physical EndpointVector or active-divisibility support is inserted. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators

def markedMemoryBirthInitialPhase {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B N : ℕ} {Z : Finset (ℤ × ℤ)}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N))
    (θ : MarkedMemoryPotentialAddress J M B N → AddCircle (1:ℝ))
    (s : MarkedRawState P M B Z) : ℂ :=
  ∏ i, ∏ k : Fin M, markedBirthLocalMultiplier σ θ (Sum.inl (i,k)) (some ((s.2.1 i k).1))

theorem markedMemoryBirthInitialPhase_norm_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B N : ℕ} {Z : Finset (ℤ × ℤ)}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N))
    (θ : MarkedMemoryPotentialAddress J M B N → AddCircle (1:ℝ))
    (s : MarkedRawState P M B Z) : ‖markedMemoryBirthInitialPhase σ θ s‖ ≤ 1 := by
  unfold markedMemoryBirthInitialPhase
  rw [norm_prod]
  apply Finset.prod_le_one₀ (fun i _ => norm_nonneg _)
  intro i _
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun k _ => norm_nonneg _) (fun k _ => markedBirthLocalMultiplier_norm_le σ θ _ _)

def markedMemoryBirthPhaseBoundaryPairing
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (i : J) → ↥(P i) → ℝ) (V : J → ℝ) {pads B N : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N))
    (θ : MarkedMemoryPotentialAddress J (pads+1) B N → AddCircle (1:ℝ)) (z₀ : Z) : ℂ :=
  ∑ s, (markedRawStateMass ν s:ℂ)*star (markedRawBoundary z₀ s)*markedMemoryBirthInitialPhase σ θ s *
    markedMemoryBirthPhaseWord ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ θ N 0 (markedRawBoundary z₀) s

set_option backward.isDefEq.respectTransparency false in
theorem markedMemoryBirthPhaseBoundary_actual_bound
    {J : Type*} [Fintype J] [decJ : DecidableEq J]
    (e : J → ℝ) (he : ∀ i, (1/10:ℝ) ≤ e i) (hinj : Function.Injective e)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (hη : Function.support η ⊆ Set.Icc 1 4) (hηnorm : ∀ u, ‖η u‖ ≤ 1)
    (q ρ G H c T A W : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    (hρ : 0 < ρ) (hρ₁ : ρ < 1) (hgap : Real.sqrt q < ρ^2)
    (hG : 0 < G) (hH : 1 ≤ H) (hc : 0 < c) (hT : 0 ≤ T) (hA : 0 ≤ A) (hW : 0 ≤ W)
    (hdepth : 100*(5*G+26) < (Fintype.card J:ℝ))
    (hψ : ∀ u, ‖ψ u‖ ≤ W) (hsupp : Function.support ψ ⊆ Set.Icc (-A) A) :
    ∀ᶠ x : ℝ in atTop, ∀ (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
      (r d₀ Y : ℝ) (w : Z → ℤ × ℤ) (z₀ : Z) (N : ℕ)
      (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (markedPadSlots x) (markedDirtyMemoryCutoff x) N))
      (θ : MarkedMemoryPotentialAddress J (markedPadSlots x) (markedDirtyMemoryCutoff x) N → AddCircle (1:ℝ))
      (orientation : ℕ → Bool),
      0 < d₀ → Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y → Y ≤ Real.exp (H*(Real.log x)^(1/5:ℝ)) →
      (∀ z, markedMinorIntegerDet z.1 (w z) = 1) →
      (∀ z ∈ Z, c ≤ |markedMinorIntegerTau r z| ∧ |markedMinorIntegerTau r z| ≤ T) →
      (∀ z v : Z, |markedMinorIntegerTau r v.1/markedMinorIntegerTau r z.1| ≤ 16) →
      let C := Real.exp ((Fintype.card J:ℝ)*(2*markedRawGhostSchurParameter q ρ/ρ))
      let ε := (Real.log x)^(-G)
      let R := markedRawEdgeCrudeActualConstant (Fintype.card J) (markedRawGhostSchurParameter q ρ) 1 W A 1 *
        (markedDirtyMemoryCutoff x+1:ℝ)^(Fintype.card J)*((Real.log x)^(G+7))^3
      let m := markedOperatorModifiedEdgeCount (MarkedMemoryBirthEdgeModified σ) N 0
      ‖markedMemoryBirthPhaseBoundaryPairing (pads := ⌊(Real.log x)^(1/100:ℝ)⌋₊)
        (markedRawActualPrimeAtom e q x) (fun i => bandReciprocalMass (markedLogPowerBand (e i) x))
        hZ ψ η d₀ Y ((Real.log x)^(G+7)) ρ orientation (markedMemoryWordVisitQ q N)
        (fun _ => markedRawDirtyGoodCutoff e x r d₀ Y w (fun _ => 1)) σ θ z₀‖ ≤
        2*C^(N+1)*ε^(N-m)*R^m := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  filter_upwards [markedMemoryBirthPhaseWord_actual_energy e he hinj ψ η hη hηnorm q ρ G H c T A W
    hq₀ hq₁ hρ hρ₁ hgap hG hH hc hT hA hW hdepth hψ hsupp,
    markedRawBoundary_actual_energy_le_two e he,markedRawActualStateMass_nonneg_eventually e he,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx hb hmass hlog
  intro Z hZ r d₀ Y w z₀ N σ θ orientation hd₀ hYlo hYhi hw hτ hbox
  let ν := markedRawActualPrimeAtom e q x
  let V := fun i => bandReciprocalMass (markedLogPowerBand (e i) x)
  let b : MarkedRawState (markedRawActualPrimeBand e x) (markedPadSlots x) (markedDirtyMemoryCutoff x) Z → ℂ :=
    markedRawBoundary z₀
  let β := markedMemoryBirthInitialPhase (P := markedRawActualPrimeBand e x) (Z := Z) σ θ
  let b₀ := fun s => star (β s)*b s
  let χg := fun _i : ℕ => markedRawDirtyGoodCutoff e x r d₀ Y w
    (fun _s : MarkedRawState (markedRawActualPrimeBand e x) (markedPadSlots x) (markedDirtyMemoryCutoff x) Z => (1:ℂ))
  let F := markedMemoryBirthPhaseWord ν V hZ ψ η d₀ Y ((Real.log x)^(G+7)) ρ orientation
    (markedMemoryWordVisitQ q N) χg σ θ N 0 b
  let C := Real.exp ((Fintype.card J:ℝ)*(2*markedRawGhostSchurParameter q ρ/ρ))
  let ε := (Real.log x)^(-G)
  let R := markedRawEdgeCrudeActualConstant (Fintype.card J) (markedRawGhostSchurParameter q ρ) 1 W A 1 *
    (markedDirtyMemoryCutoff x+1:ℝ)^(Fintype.card J)*((Real.log x)^(G+7))^3
  let m := markedOperatorModifiedEdgeCount (MarkedMemoryBirthEdgeModified σ) N 0
  let k := C^(N+1)*ε^(N-m)*R^m
  have hμ : ∀ s : MarkedRawState (markedRawActualPrimeBand e x) (markedPadSlots x) (markedDirtyMemoryCutoff x) Z,
      0 ≤ markedRawStateMass ν s := hmass q hq₀ hq₁ _ _ Z
  have hR : 0 ≤ R := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hv := markedRawGhostSchurParameter_ge_one q ρ
    dsimp [R,markedRawEdgeCrudeActualConstant]
    positivity
  have hk : 0 ≤ k := by
    dsimp only [k]
    exact mul_nonneg (mul_nonneg (pow_nonneg (Real.exp_pos _).le _)
      (pow_nonneg (Real.rpow_nonneg (zero_le_one.trans hlog) _) _)) (pow_nonneg hR _)
  have hb₁ : (∑ s, markedRawStateMass ν s*‖b s‖^2) ≤ 2 := hb q hq₀ hq₁ _ Z z₀
  have hb₀ : (∑ s, markedRawStateMass ν s*‖b₀ s‖^2) ≤ 2 :=
    (markedWeightedEnergy_bounded_multiplier (markedRawStateMass ν) hμ (fun s => star (β s)) b
      (fun s => by simpa only [norm_star] using markedMemoryBirthInitialPhase_norm_le σ θ s)).trans hb₁
  have hF : (∑ s, markedRawStateMass ν s*‖F s‖^2) ≤ k^2*∑ s, markedRawStateMass ν s*‖b s‖^2 := by
    have hh := hx Z hZ r d₀ Y w N σ θ orientation (fun _ _ => 1) (markedMemoryWordVisitQ q N) b
      hd₀ hYlo hYhi hw hτ hbox (by intro i s; norm_num) (fun _ _ _ _ _ => rfl)
      (markedMemoryWordVisitQ_bounds hq₀ hq₁ N) (markedRawBoundary_symmetric z₀) N 0
    change (∑ s, markedRawStateMass ν s*‖F s‖^2) ≤
      (C^(N+1)*markedOperatorEdgeBudget (fun i => if MarkedMemoryBirthEdgeModified σ i then R else ε) N 0)^2*
        ∑ s, markedRawStateMass ν s*‖b s‖^2 at hh
    rw [markedOperatorEdgeBudget_mixed] at hh
    simpa only [k,m,mul_assoc] using hh
  have hbound := markedWeightedBoundary_two_sided_norm_le (markedRawStateMass ν) hμ b₀ b F
    (by norm_num : (0:ℝ) ≤ 2) hk hb₀ hb₁ hF
  have heq : markedMemoryBirthPhaseBoundaryPairing ν V hZ ψ η d₀ Y ((Real.log x)^(G+7)) ρ orientation
      (markedMemoryWordVisitQ q N) χg σ θ z₀ = ∑ s, (markedRawStateMass ν s:ℂ)*star (b₀ s)*F s := by
    apply Finset.sum_congr rfl
    intro s _
    change (markedRawStateMass ν s:ℂ)*star (b s)*β s*F s =
      (markedRawStateMass ν s:ℂ)*star (b₀ s)*F s
    dsimp only [b₀]
    rw [star_mul,star_star]
    ring
  change ‖markedMemoryBirthPhaseBoundaryPairing ν V hZ ψ η d₀ Y ((Real.log x)^(G+7)) ρ orientation
    (markedMemoryWordVisitQ q N) χg σ θ z₀‖ ≤ 2*C^(N+1)*ε^(N-m)*R^m
  rw [heq]
  exact hbound.trans_eq (by dsimp only [k]; ring)

end ArtinMatthews
