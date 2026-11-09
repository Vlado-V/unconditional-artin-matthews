module

public import ArtinMatthews.MarkedMemoryPositivePivotWordActual
public import ArtinMatthews.MarkedMemoryBirthEventPositive
public import ArtinMatthews.MarkedMemoryInitialPivotSource


set_option backward.privateInPublic true
@[expose] public section

/-! The actual positive boundary pays exactly one tilted atom per
permutation rank. The original empty-memory boundary and ordered active
tuple measure are retained, including their explicit initial cost. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false in
theorem markedMemoryPositivePivotBoundary_actual_bound
    {J : Type*} [Fintype J] [decJ : DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) {q ρ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hgap : Real.sqrt q < ρ^2) :
    ∀ᶠ x : ℝ in atTop, ∀ (pads B N : ℕ) (Z : Finset (ℤ × ℤ))
      (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
      (r d₀ Y Q H W A : ℝ) (w : Z → ℤ × ℤ)
      (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N)) (z₀ : Z)
      (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
      (χ : ℕ → MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ),
      1 ≤ Y → 1 ≤ Q → 0 ≤ H → 0 ≤ W → 0 ≤ A →
      (∀ u,‖η u‖ ≤ H) → (∀ u,‖ψ u‖ ≤ W) → (∀ u,ψ u≠0 → |u| ≤ A) →
      (∀ z,markedMinorIntegerDet z.1 (w z)=1) →
      (∀ z : Z,markedMinorIntegerTau r z.1≠0) →
      (∀ z v : Z,|markedMinorIntegerTau r v.1/markedMinorIntegerTau r z.1| ≤ 16) →
      (∀ j,0 ≤ qStage j ∧ qStage j ≤ Real.sqrt q) → (∀ j s,‖χ j s‖ ≤ 1) →
      let ν := markedRawActualPrimeAtom e q x
      let V := fun i => bandReciprocalMass (markedLogPowerBand (e i) x)
      let v₀ := markedRawGhostSchurParameter q ρ
      let Cg := Real.exp ((Fintype.card J:ℝ)*(2*v₀/ρ))
      let R := markedRawEdgeCrudeActualConstant (Fintype.card J) v₀ H W A 1*(B+1:ℝ)^(Fintype.card J)*Q^3
      markedMemoryPositivePivotBoundary ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ z₀ ≤
        (2:ℝ)^(Fintype.card J*(pads+1))*Cg^(N+1)*R^N*
          (markedMemoryBirthAtomEnvelope x)^(markedBirthPermutationRank σ) := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  filter_upwards [markedMemoryPositivePivotWord_actual_bound e he hq₀ hq₁ hρ hρ₁ hgap,
    markedMemoryInitialPivot_actual_source_eventually e he,
    markedMemoryBirthAtom_actual_eventually e he] with x hword hsource hatom
  intro pads B N Z hZ ψ η r d₀ Y Q H W A w σ z₀ orientation qStage χ
    hY hQ hH hW hA hη hψ hsupp hw hτ hbox hstage hχ
  dsimp only
  let ν := markedRawActualPrimeAtom e q x
  let V := fun i => bandReciprocalMass (markedLogPowerBand (e i) x)
  let v₀ := markedRawGhostSchurParameter q ρ
  let Cg := Real.exp ((Fintype.card J:ℝ)*(2*v₀/ρ))
  let R := markedRawEdgeCrudeActualConstant (Fintype.card J) v₀ H W A 1*(B+1:ℝ)^(Fintype.card J)*Q^3
  let Δ := markedMemoryBirthAtomEnvelope x
  let C := Cg^(N+1)*R^N*Δ^(markedMemoryPivotTailCount σ N 0)
  let S := Δ^(markedMemoryStageNonpivots σ 0).card*(2:ℝ)^(Fintype.card J*(pads+1))
  have hv₀ : 0 < v₀ := zero_lt_one.trans_le (markedRawGhostSchurParameter_ge_one q ρ)
  have hR : 0 ≤ R := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [R,markedRawEdgeCrudeActualConstant]
    positivity
  have hΔ : 0 ≤ Δ := (markedMemoryBirthAtomEnvelope_pos x).le
  have hCg : 0 ≤ Cg := (Real.exp_pos _).le
  have hC : 0 ≤ C := mul_nonneg
    (mul_nonneg (pow_nonneg hCg _) (pow_nonneg hR _)) (pow_nonneg hΔ _)
  have hν : ∀ j p,0 ≤ ν j p := fun j p => (hatom q hq₀ hq₁ j p).1
  have hwb := hword pads B N Z hZ ψ η r d₀ Y Q H W A w σ orientation qStage χ
    hY hQ hH hW hA hη hψ hsupp hw hτ hbox hstage hχ
    (fun _ t => ‖markedRawBoundary z₀ t‖) (fun _ t => markedRawBoundary_norm_le_schur z₀ hv₀ t)
  have hsb := hsource q hq₀ hq₁ (pads+1) B N Z z₀ v₀ σ (fun _ => none)
  have hb := markedMemoryPositivePivotBoundary_le ν hν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ z₀
    v₀ C S hC hwb hsb
  apply hb.trans_eq
  calc
    _ = (2:ℝ)^(Fintype.card J*(pads+1))*Cg^(N+1)*R^N*
        (Δ^(markedMemoryStageNonpivots σ 0).card*Δ^(markedMemoryPivotTailCount σ N 0)) := by
      dsimp [C,S]
      ring
    _ = _ := by rw [← pow_add,markedMemoryPivotTailCount_rank]

end ArtinMatthews
