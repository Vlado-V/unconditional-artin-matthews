module

public import ArtinMatthews.MarkedMemoryPositivePivotWord
public import ArtinMatthews.MarkedMemoryPivotRowsActual
public import ArtinMatthews.MarkedMemoryStageBudget


set_option backward.privateInPublic true
@[expose] public section

/-! Actual positive conditional word bound. All ghost and edge row
estimates are discharged using the original tilted law and geometry.
No signed norm estimate is substituted for an absolute row estimate. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false in
theorem markedMemoryPositivePivotWord_actual_bound
    {J : Type*} [Fintype J] [decJ : DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) {q ρ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hgap : Real.sqrt q < ρ^2) :
    ∀ᶠ x : ℝ in atTop, ∀ (pads B N : ℕ) (Z : Finset (ℤ × ℤ))
      (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
      (r d₀ Y Q H W A : ℝ) (w : Z → ℤ × ℤ)
      (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N))
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
      ∀ (f : (MarkedMemoryPotentialAddress J (pads+1) B N → Option Nat.Primes) →
        MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℝ),
      (∀ old s,f old s ≤ markedRawMemorySchurWeight v₀ s.2.2) →
      ∀ old s,markedMemoryPositivePivotWord ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ N 0 f old s ≤
        Cg^(N+1)*R^N*(markedMemoryBirthAtomEnvelope x)^(markedMemoryPivotTailCount σ N 0)*
          markedRawMemorySchurWeight v₀ s.2.2 := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  filter_upwards [markedMemoryGhostPivot_choice_row_eventually e he hq₀ hq₁ hρ hgap,
    markedMemoryEdgePivot_choice_row_eventually e he] with x hghost hedge
  intro pads B N Z hZ ψ η r d₀ Y Q H W A w σ orientation qStage χ
    hY hQ hH hW hA hη hψ hsupp hw hτ hbox hstage hχ
  dsimp only
  intro f hf old s
  let ν := markedRawActualPrimeAtom e q x
  let V := fun i => bandReciprocalMass (markedLogPowerBand (e i) x)
  let v₀ := markedRawGhostSchurParameter q ρ
  let Cg := Real.exp ((Fintype.card J:ℝ)*(2*v₀/ρ))
  let R := markedRawEdgeCrudeActualConstant (Fintype.card J) v₀ H W A 1*(B+1:ℝ)^(Fintype.card J)*Q^3
  let Δ := markedMemoryBirthAtomEnvelope x
  let State := MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z
  let Memo := MarkedMemoryPotentialAddress J (pads+1) B N → Option Nat.Primes
  let ghost := markedMemoryPositiveGhostPivotAt ν V qStage ρ hZ σ
  let edge := markedMemoryPositiveEdgePivotAt ν V hZ ψ η d₀ Y Q ρ orientation χ σ
  let g := fun j => Δ^(markedMemoryStageNonpivots σ (2*j+1)).card*Cg
  let k := fun j => Δ^(markedMemoryStageNonpivots σ (2*j+2)).card*R
  let weight := fun s : State => markedRawMemorySchurWeight v₀ s.2.2
  have hv₀ : 1 ≤ v₀ := markedRawGhostSchurParameter_ge_one q ρ
  have hv₀p : 0 < v₀ := zero_lt_one.trans_le hv₀
  have hΔ : 0 ≤ Δ := (markedMemoryBirthAtomEnvelope_pos x).le
  have hR : 0 ≤ R := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [R,markedRawEdgeCrudeActualConstant]
    positivity
  have hg : ∀ j,0 ≤ g j := fun _ => mul_nonneg (pow_nonneg hΔ _) (Real.exp_pos _).le
  have hk : ∀ j,0 ≤ k j := fun _ => mul_nonneg (pow_nonneg hΔ _) hR
  have hgBound : ∀ j (F : Memo → State → ℝ) C,0 ≤ C →
      (∀ a s,F a s ≤ C*weight s) → ∀ a s,ghost j F a s ≤ C*g j*weight s := by
    intro j F C hC hF a v
    by_cases hj : j<N+1
    · dsimp only [ghost,markedMemoryPositiveGhostPivotAt]
      rw [dite_eq_left hj]
      exact markedMemoryPositiveGhostPivot_bound ν V (qStage j) ρ v₀ hZ σ ⟨j,hj⟩ F hC hv₀p
        hF a v (hghost (pads+1) B N (pads+1) σ ⟨j,hj⟩ a (qStage j)
          (hstage j).1 (hstage j).2 Z hZ v)
    · dsimp only [ghost,markedMemoryPositiveGhostPivotAt]
      rw [dite_eq_right hj]
      exact mul_nonneg (mul_nonneg hC (hg j)) (markedRawMemorySchurWeight_pos hv₀p _).le
  have hηstar : ∀ u,‖star (η u)‖ ≤ H := by simpa only [norm_star] using hη
  have hψstar := markedRawEdgeAdjointCutoff_bounds ψ hψ
    (show Function.support ψ ⊆ Set.Icc (-A) A from fun u hu => abs_le.mp (hsupp u hu))
  have heBound : ∀ j (F : Memo → State → ℝ) C,0 ≤ C →
      (∀ a s,F a s ≤ C*weight s) → ∀ a s,edge j F a s ≤ C*k j*weight s := by
    intro j F C hC hF a v
    by_cases hj : j<N
    · dsimp only [edge,markedMemoryPositiveEdgePivotAt]
      rw [dite_eq_left hj]
      by_cases ho : orientation j
      · rw [ite_eq_left ho]
        exact markedMemoryPositiveEdgePivot_bound ν V hZ _ _ d₀ Y Q ρ v₀ _ σ ⟨j,hj⟩ F hC hv₀p hF a v
          (hedge (pads+1) B N σ ⟨j,hj⟩ a pads Z hZ _ _ r d₀ Y Q q ρ H W A v₀
            (fun s => star (χ j s)) v (w v.1) hY hQ hq₀ hq₁ hρ.le hρ₁ hH hW hA hv₀
            hηstar hψstar.1 (fun u hu => abs_le.mpr (hψstar.2 hu))
            (fun s => by simpa only [norm_star] using hχ j s) (hw v.1) (hτ v.1)
            (fun z hz => hbox v.1 ⟨z,hz⟩))
      · rw [ite_eq_right ho]
        exact markedMemoryPositiveEdgePivot_bound ν V hZ ψ η d₀ Y Q ρ v₀ (χ j) σ ⟨j,hj⟩ F hC hv₀p hF a v
          (hedge (pads+1) B N σ ⟨j,hj⟩ a pads Z hZ ψ η r d₀ Y Q q ρ H W A v₀ (χ j) v (w v.1)
            hY hQ hq₀ hq₁ hρ.le hρ₁ hH hW hA hv₀ hη hψ hsupp (hχ j)
            (hw v.1) (hτ v.1) (fun z hz => hbox v.1 ⟨z,hz⟩))
    · dsimp only [edge,markedMemoryPositiveEdgePivotAt]
      rw [dite_eq_right hj]
      exact mul_nonneg (mul_nonneg hC (hk j)) (markedRawMemorySchurWeight_pos hv₀p _).le
  have hword := markedConditionalWord_bound ghost edge g k weight hg hk hgBound heBound f
    (C := 1) zero_le_one (by simpa only [one_mul] using hf) N 0 old s
  simpa only [one_mul,ghost,edge,g,k,weight,markedMemoryPositivePivotWord,
    markedMemory_conditional_budget,ν,V,Cg,R,Δ] using hword

end ArtinMatthews
