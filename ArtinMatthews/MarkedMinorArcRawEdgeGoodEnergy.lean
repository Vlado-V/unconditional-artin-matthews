module

public import ArtinMatthews.MarkedMinorArcDirtySectorActual


set_option backward.privateInPublic true
@[expose] public section

/-! The full actual edge on the two-sided first-good and beta-good
projection. The three estimated pieces exhaust all literal store/promote
choices, including pure stores. No row or column bound is a hypothesis. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators

theorem markedRawEdge_good_actual_energy
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (hinj : Function.Injective e)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (hη : Function.support η ⊆ Set.Icc 1 4) (hηnorm : ∀ t,‖η t‖ ≤ 1)
    (G H c T A W ρ : ℝ) (hG : 0 < G) (hH : 1 ≤ H) (hc : 0 < c)
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hW : 0 ≤ W) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1)
    (hdepth : 100*(5*G+26)<(Fintype.card J:ℝ))
    (hψnorm : ∀ t,‖ψ t‖ ≤ W) (hsupp : Function.support ψ ⊆ Set.Icc (-A) A) :
    ∀ᶠ x : ℝ in atTop, ∀ (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
      (q r d₀ Y : ℝ) (w : Z → ℤ × ℤ)
      (χ f : MarkedRawState (markedRawActualPrimeBand e x) (markedPadSlots x) (markedDirtyMemoryCutoff x) Z → ℂ),
      0 ≤ q → q ≤ 1 → 0 < d₀ →
      Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y → Y ≤ Real.exp (H*(Real.log x)^(1/5:ℝ)) →
      (∀ z,markedMinorIntegerDet z.1 (w z)=1) →
      (∀ z ∈ Z,c ≤ |markedMinorIntegerTau r z| ∧ |markedMinorIntegerTau r z| ≤ T) →
      (∀ z v : Z,|markedMinorIntegerTau r v.1/markedMinorIntegerTau r z.1| ≤ 16) →
      (∀ s,‖χ s‖ ≤ 1) →
      (∀ z a,MarkedRawMemorySymmetric (fun m => χ (z,(a,m)))) →
      (∀ z a,MarkedRawMemorySymmetric (fun m => f (z,(a,m)))) →
      (∑ s,markedRawStateMass (markedRawActualPrimeAtom e q x) s *
        ‖markedRawEdgeSymmetrized (markedRawActualPrimeAtom e q x)
          (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) hZ ψ η d₀ Y
          ((Real.log x)^(G+7)) ρ (markedRawDirtyGoodCutoff e x r d₀ Y w χ) f s‖^2) ≤
        ((Real.log x)^(-G))^2 * ∑ s,markedRawStateMass (markedRawActualPrimeAtom e q x) s*‖f s‖^2 := by
  have hdepth' : 100*(2*(G+1)+3*(G+7)+3)<(Fintype.card J:ℝ) := by nlinarith
  have hG' : 0 ≤ G+1 := by linarith
  have hA₀ : 0 ≤ G+7 := by linarith
  filter_upwards [markedRawEdge_dirty_sector_actual_energy e he hinj ψ η 1 c T A 1 W ρ (G+7) (G+1)
      le_rfl hc hT hA zero_le_one hW hρ₀ hρ₁ hA₀ hG' hdepth' hηnorm hψnorm hsupp,
    marked_minor_actual_edge_clean_symmetrized_energy e he hinj ψ η hη hηnorm
      (G := G+1) (H := H) (c := c) (L := T) (K := A) (by linarith) hH hc hT hA hsupp,
    markedDirty_actual_band_transfer_eventually e he,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (3:ℝ))]
    with x hsector hclean htransfer hlog
  intro Z hZ q r d₀ Y w χ f hq₀ hq₁ hd₀ hYlo hYhi hw hτ hbox hχ hχsym hf
  let ν := markedRawActualPrimeAtom e q x
  let V := fun j => bandReciprocalMass (markedLogPowerBand (e j) x)
  let χg := markedRawDirtyGoodCutoff e x r d₀ Y w χ
  let K := fun (_ _ : J → Bool) => markedRawEdgeJointCoefficient hZ ψ η d₀ Y ((Real.log x)^(G+7)) ρ χg
  let Fc := markedRawEdgeCleanSymmetrized ν V hZ ψ η d₀ Y ((Real.log x)^(G+7)) ρ χg f
  let Fp := markedRawEdgePatternSymmetrized ν (fun j => ((V j)⁻¹:ℝ)) (fun _ => 1) hZ
    (markedRawEdgePromotedKernel K) f
  let Fs := markedRawEdgePatternSymmetrized ν (fun j => ((V j)⁻¹:ℝ)) (fun _ => 1) hZ
    (markedRawEdgeStoreOnlyKernel K) f
  let E : ℝ := ∑ s,markedRawStateMass ν s*‖f s‖^2
  let ε : ℝ := (Real.log x)^(-(G+1))
  have ht := htransfer q hq₀ hq₁
  have hμ : ∀ s : MarkedRawState (markedRawActualPrimeBand e x) (markedPadSlots x) (markedDirtyMemoryCutoff x) Z,
      0 ≤ markedRawStateMass ν s := markedRawStateMass_nonneg ν ht.1
  have hE : 0 ≤ E := Finset.sum_nonneg (fun s _ => mul_nonneg (hμ s) (sq_nonneg _))
  have hsectors := hsector Z hZ r d₀ Y q w χ f hYlo hq₀ hq₁ hw hτ hbox hχ hχsym hf
  have hp : (∑ s,markedRawStateMass ν s*‖Fp s‖^2) ≤ ε^2*E := hsectors.1
  have hs : (∑ s,markedRawStateMass ν s*‖Fs s‖^2) ≤ ε^2*E := hsectors.2
  have hexp : G+1+6=G+7 := by ring
  simp only [hexp] at hclean
  have hcl : (∑ s,markedRawStateMass ν s*‖Fc s‖^2) ≤ ε^2*E := by
    exact hclean (markedDirtyMemoryCutoff x) Z hZ q r d₀ Y ρ w
      (markedRawDirtySecondGoodCutoff e x r w χ) hq₀ hq₁ hd₀ hρ₀ hρ₁.le hYlo hYhi hw hτ hbox
      (markedRawDirtySecondGoodCutoff_norm_le e x r w χ hχ) f
  have hsplit : markedRawEdgeSymmetrized ν V hZ ψ η d₀ Y ((Real.log x)^(G+7)) ρ χg f = Fc+Fp+Fs := by
    have hd : markedRawEdgeDirtySymmetrized ν V hZ ψ η d₀ Y ((Real.log x)^(G+7)) ρ χg f = Fp+Fs :=
      (markedRawEdgeDirtySymmetrized_eq_pattern ν V hZ ψ η d₀ Y ((Real.log x)^(G+7)) ρ χg f).trans
        (markedRawEdgeDirtySymmetrized_eq_promoted_add_storeOnly ν (fun j => ((V j)⁻¹:ℝ)) (fun _ => 1) hZ K f)
    exact (markedRawEdgeSymmetrized_eq_clean_add_dirty ν V hZ ψ η d₀ Y ((Real.log x)^(G+7)) ρ χg f).trans
      ((congrArg (fun F => Fc+F) hd).trans (add_assoc _ _ _).symm)
  change (∑ s,markedRawStateMass ν s *
    ‖markedRawEdgeSymmetrized ν V hZ ψ η d₀ Y ((Real.log x)^(G+7)) ρ χg f s‖^2) ≤ _
  rw [hsplit]
  calc
    _ ≤ 3*((∑ s,markedRawStateMass ν s*‖Fc s‖^2)+
        (∑ s,markedRawStateMass ν s*‖Fp s‖^2)+(∑ s,markedRawStateMass ν s*‖Fs s‖^2)) :=
      markedDirty_weighted_three_energy_le (markedRawStateMass ν) hμ Fc Fp Fs
    _ ≤ 3*(ε^2*E+ε^2*E+ε^2*E) := by gcongr
    _ = (9*ε^2)*E := by ring
    _ ≤ ((Real.log x)^(-G))^2*E :=
      mul_le_mul_of_nonneg_right (markedDirty_three_log_budget hlog) hE

end
end ArtinMatthews
