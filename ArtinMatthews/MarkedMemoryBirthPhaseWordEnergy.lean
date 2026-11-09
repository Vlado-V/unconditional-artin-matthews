module

public import ArtinMatthews.MarkedMemoryBirthPhaseWord


set_option backward.privateInPublic true
@[expose] public section

/-! Actual signed/crude mixed word energy. Every ghost has the proved fixed
constant. Only edges meeting a moved birth address pay the crude polynomial;
all other edges retain the signed full-good logarithmic contraction. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false in
theorem markedMemoryBirthPhaseWord_actual_energy
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
      (N : ℕ)
      (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (markedPadSlots x) (markedDirtyMemoryCutoff x) N))
      (θ : MarkedMemoryPotentialAddress J (markedPadSlots x) (markedDirtyMemoryCutoff x) N → AddCircle (1:ℝ))
      (orientation : ℕ → Bool)
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
      let R := markedRawEdgeCrudeActualConstant (Fintype.card J) (markedRawGhostSchurParameter q ρ) 1 W A 1 *
        (markedDirtyMemoryCutoff x+1:ℝ)^(Fintype.card J)*((Real.log x)^(G+7))^3
      let E := fun i => if MarkedMemoryBirthEdgeModified σ i then R else ε
      (∑ s, markedRawStateMass ν s *
        ‖markedMemoryBirthPhaseWord ν V hZ ψ η d₀ Y ((Real.log x)^(G+7)) ρ orientation qStage
          (fun i => markedRawDirtyGoodCutoff e x r d₀ Y w (χ i)) σ θ n j f s‖^2) ≤
        (C^(n+1)*markedOperatorEdgeBudget E n j)^2 * ∑ s, markedRawStateMass ν s*‖f s‖^2 := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  have hηstar : Function.support (fun u => star (η u)) ⊆ Set.Icc 1 4 := by
    intro u hu
    apply hη
    intro h
    apply hu
    change star (η u) = 0
    rw [h,star_zero]
  have hηstarnorm : ∀ u, ‖star (η u)‖ ≤ 1 := by simpa only [norm_star] using hηnorm
  have hψstar := markedRawEdgeAdjointCutoff_bounds ψ hψnorm hsupp
  filter_upwards [markedRawGhostModifiedApply_actual_energy_eventually e he hq₀ hq₁ hρ hgap,
    markedRawEdge_good_actual_energy e he hinj ψ η hη hηnorm G H c T A W ρ
      hG hH hc hT hA hW hρ.le hρ₁ hdepth hψnorm hsupp,
    markedRawEdge_good_actual_energy e he hinj (markedRawEdgeAdjointCutoff ψ)
      (fun u => star (η u)) hηstar hηstarnorm G H c T A W ρ
      hG hH hc hT hA hW hρ.le hρ₁ hdepth hψstar.1 hψstar.2,
    markedRawEdgeModifiedSymmetrized_actual_crude_energy_eventually e he hinj,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
    with x hghost hedge hgeometric hcrude hlog
  intro Z hZ r d₀ Y w N σ θ orientation χ qStage f hd₀ hYlo hYhi hw hτ hbox hχ hχsym hstage hf n j
  let ν := markedRawActualPrimeAtom e q x
  let V := fun i => bandReciprocalMass (markedLogPowerBand (e i) x)
  let v₀ := markedRawGhostSchurParameter q ρ
  let Q := (Real.log x)^(G+7)
  let χg := fun i => markedRawDirtyGoodCutoff e x r d₀ Y w (χ i)
  let State := MarkedRawState (markedRawActualPrimeBand e x) (markedPadSlots x) (markedDirtyMemoryCutoff x) Z
  let S := fun F : State → ℂ => ∀ z a, MarkedRawMemorySymmetric (fun m => F (z,(a,m)))
  let C := Real.exp ((Fintype.card J:ℝ)*(2*v₀/ρ))
  let ε := (Real.log x)^(-G)
  let R := markedRawEdgeCrudeActualConstant (Fintype.card J) v₀ 1 W A 1 *
    (markedDirtyMemoryCutoff x+1:ℝ)^(Fintype.card J)*Q^3
  let E := fun i => if MarkedMemoryBirthEdgeModified σ i then R else ε
  let ghost := fun i => markedRawGhostBirthModifiedApply (M := markedPadSlots x)
    (B := markedDirtyMemoryCutoff x) ν V (qStage i) ρ hZ
    (markedMemoryGhostBirthPhaseAt σ θ i)
  let edge := fun i => if orientation i then
    markedRawEdgeModifiedSymmetrized ν V hZ (markedRawEdgeAdjointCutoff ψ) (fun u => star (η u))
      d₀ Y Q ρ (fun s => star (χg i s))
      (markedRawEdgeBirthModifier (markedMemoryEdgeBirthPhaseAt σ θ i))
    else markedRawEdgeModifiedSymmetrized ν V hZ ψ η d₀ Y Q ρ (χg i)
      (markedRawEdgeBirthModifier (markedMemoryEdgeBirthPhaseAt σ θ i))
  have hχg : ∀ i z a, MarkedRawMemorySymmetric (fun m => χg i (z,(a,m))) :=
    fun i => markedRawDirtyGoodCutoff_symmetric e x r d₀ Y w (χ i) (hχsym i)
  have hχgnorm (i : ℕ) : ∀ s, ‖χg i s‖ ≤ 1 :=
    markedRawDirtyGoodCutoff_norm_le e x r d₀ Y w (χ i) (hχ i)
  have hχgstar : ∀ i z a, MarkedRawMemorySymmetric (fun m => star (χg i (z,(a,m)))) :=
    fun i z a m τ => congrArg star (hχg i z a m τ)
  have hcutstar (i : ℕ) : (fun s => star (χg i s)) =
      markedRawDirtyGoodCutoff e x r d₀ Y w (fun s => star (χ i s)) := by
    funext s
    dsimp only [χg]
    rw [markedRawDirtyGoodCutoff_eq_ite,markedRawDirtyGoodCutoff_eq_ite]
    split_ifs <;> simp only [star_zero]
  have hgS : ∀ i F, S F → S (ghost i F) :=
    fun i F hF => markedRawGhostBirthModifiedApply_symmetric ν V (qStage i) ρ hZ _ F hF
  have heS : ∀ i F, S F → S (edge i F) := by
    intro i F hF
    by_cases hi : orientation i
    · simp only [edge,ite_eq_left hi]
      exact markedRawEdgeBirthModifiedSymmetrized_symmetric ν V hZ _ _ _ _ _ _ _ F _ (hχgstar i) hF
    · simp only [edge,ite_eq_right hi]
      exact markedRawEdgeBirthModifiedSymmetrized_symmetric ν V hZ _ _ _ _ _ _ _ F _ (hχg i) hF
  have hY : 1 ≤ Y := (Real.one_le_exp (Real.rpow_nonneg (zero_le_one.trans hlog) _)).trans hYlo
  have hQ : 1 ≤ Q := Real.one_le_rpow hlog (by linarith : 0 ≤ G+7)
  have hcrudeE (ψ' : SchwartzMap ℝ ℂ) (η' : ℝ → ℂ)
      (hη' : ∀ u, ‖η' u‖ ≤ 1) (hψ' : ∀ u, ‖ψ' u‖ ≤ W)
      (hsupp' : Function.support ψ' ⊆ Set.Icc (-A) A)
      (χ' : State → ℂ) (hχ' : ∀ s, ‖χ' s‖ ≤ 1)
      (hχ'sym : ∀ z a, MarkedRawMemorySymmetric (fun m => χ' (z,(a,m))))
      (F : State → ℂ) (hF : S F) (i : ℕ) :
      (∑ s, markedRawStateMass ν s*‖markedRawEdgeModifiedSymmetrized ν V hZ ψ' η' d₀ Y Q ρ χ'
        (markedRawEdgeBirthModifier (markedMemoryEdgeBirthPhaseAt σ θ i)) F s‖^2) ≤
        R^2*∑ s, markedRawStateMass ν s*‖F s‖^2 := by
    exact hcrude ⌊(Real.log x)^(1/100:ℝ)⌋₊ (markedDirtyMemoryCutoff x) Z hZ ψ' η' r d₀ Y Q q ρ
      1 W A v₀ w χ' F (markedRawEdgeBirthModifier (markedMemoryEdgeBirthPhaseAt σ θ i))
      hY hQ hq₀ hq₁ hρ.le hρ₁.le zero_le_one hW hA (markedRawGhostSchurParameter_ge_one q ρ)
      hη' hψ' (fun u hu => abs_le.mpr ⟨by linarith [(hsupp' hu).1],(hsupp' hu).2⟩)
      hχ' (fun s c => markedRawEdgeBirthModifier_norm_le _ (markedMemoryEdgeBirthPhaseAt_norm_le σ θ i) s c)
      hχ'sym hF hw (fun z => abs_pos.mp (hc.trans_le (hτ z.1 z.2).1)) hbox
  apply markedOperatorWord_variable_energy (markedRawStateMass ν) S ghost edge hgS heS C E
  · intro i F hF
    exact hghost (qStage i) (hstage i).1 (hstage i).2 _ _ Z hZ
      (fun s c => markedMemoryGhostBirthPhaseAt σ θ i c.sizes.1 c.births) F
      (fun s c => markedMemoryGhostBirthPhaseAt_norm_le σ θ i c.sizes.1 c.births) hF
  · intro i F hF
    by_cases hm : MarkedMemoryBirthEdgeModified σ i
    · simp only [E,ite_eq_left hm]
      by_cases hi : orientation i
      · simp only [edge,ite_eq_left hi]
        exact hcrudeE _ _ hηstarnorm hψstar.1 hψstar.2 _
          (by intro s; simpa only [norm_star] using hχgnorm i s) (hχgstar i) F hF i
      · simp only [edge,ite_eq_right hi]
        exact hcrudeE ψ η hηnorm hψnorm hsupp (χg i) (hχgnorm i) (hχg i) F hF i
    · simp only [E,ite_eq_right hm]
      by_cases hi : orientation i
      · simp only [edge,ite_eq_left hi]
        rw [markedMemoryEdgeBirthPhaseAtApply_unmodified ν V hZ _ _ d₀ Y Q ρ _ σ θ i hm F]
        erw [hcutstar i]
        exact hgeometric Z hZ q r d₀ Y w (fun s => star (χ i s)) F hq₀ hq₁ hd₀ hYlo hYhi hw hτ hbox
          (by simpa only [norm_star] using hχ i)
          (fun z a m τ => congrArg star (hχsym i z a m τ)) hF
      · simp only [edge,ite_eq_right hi]
        rw [markedMemoryEdgeBirthPhaseAtApply_unmodified ν V hZ _ _ d₀ Y Q ρ _ σ θ i hm F]
        exact hedge Z hZ q r d₀ Y w (χ i) F hq₀ hq₁ hd₀ hYlo hYhi hw hτ hbox (hχ i) (hχsym i) hF
  · exact hf

end ArtinMatthews
