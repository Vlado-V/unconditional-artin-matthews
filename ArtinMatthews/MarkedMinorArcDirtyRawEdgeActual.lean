module

public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeRow
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeActualFresh
public import ArtinMatthews.MarkedMinorArcDirtyRawEpsilon


set_option backward.privateInPublic true
@[expose] public section

/-! Actual raw-delta edge row with literal log-prime atoms and promotion
normalizers. The constant is independent of the marking-band exponents. -/
noncomputable section
namespace ArtinMatthews

open Filter
open scoped BigOperators Topology

def markedDirtyActualRowConstant (K : ℕ) (ρ H W : ℝ) : ℝ :=
  (2/Real.log 2)^K*H^2*W*(2:ℝ)^K*markedDirtyRawRowConstant K ρ

set_option backward.isDefEq.respectTransparency false in
theorem markedDirtyRawEdge_actual_delta_row_eventually {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) (hinj : Function.Injective e)
    (I : Finset J) (jstar : J) (hstar : jstar ∈ I) :
    ∀ᶠ x : ℝ in atTop, ∀ (pads B : ℕ) (Z : Finset (ℤ × ℤ))
      (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ η : ℝ → ℂ) (d₀ Y q ρ H W : ℝ)
      (χ : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ)
      (s : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z) (w : ℤ × ℤ) (r : ℝ) (Q : Finset ℤ),
      1 ≤ B → 0 ≤ q → q ≤ 1 → 0 ≤ ρ → ρ < 1 → 0 ≤ H → 0 ≤ W →
      (∀ t, ‖η t‖ ≤ H) → (∀ t, ‖ψ t‖ ≤ W) → (∀ s, ‖χ s‖ ≤ 1) →
      (∀ j, Function.Injective (s.2.1 j)) → markedMinorIntegerDet s.1.1 w=1 →
      markedMinorIntegerTau r s.1.1 ≠ 0 →
      (∀ v ∈ Z, |markedMinorIntegerTau r v/markedMinorIntegerTau r s.1.1| ≤ 16) →
      markedDirtyRawEdgeTrials s.2.1 s.2.2 (I.erase jstar) ⊆ Q →
      ((markedMinorIntegerTau r w/markedMinorIntegerTau r s.1.1:ℝ):AddCircle (1:ℝ)) ∉
        {a | Real.exp (-((Real.log x)^(e jstar))/4) ≤
          markedPairFailureProbability Q
            (markedFreshIntegerProduct (fun j : ↥(Finset.univ \ I) => e j.1) x)
            (markedFreshHarmonicLaw (fun j : ↥(Finset.univ \ I) => e j.1) x)
            (100*Real.exp (-((Real.log x)^(e jstar)))) a} →
      markedDirtyRawEdgeDeltaRow (markedRawActualPrimeAtom e q x)
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) hZ ψ η d₀ Y ρ χ s I ≤
        markedDirtyActualRowConstant (Fintype.card J) ρ H W*
          ((B:ℝ)*(pads+1:ℝ)⁻¹^(Fintype.card J)+(B:ℝ)^(Fintype.card J)*
            Real.exp (-((Real.log x)^(1/10:ℝ))/4)) := by
  classical
  let eFresh : ↥(Finset.univ \ I) → ℝ := fun j => e j.1
  have hVF : ∀ᶠ x : ℝ in atTop, ∀ j, Real.log 2/2 ≤ bandReciprocalMass (markedLogPowerBand (e j) x) :=
    eventually_all.mpr (fun j => (marked_log_power_band_mass_eventually (show 0 < e j by linarith [he j])).mono
      (fun _ hx => hx.1.le))
  filter_upwards [hVF,marked_actual_tilted_atom_comparison_eventually e he,
    markedRawDirty_delta_row_epsilon_eventually e he hinj eFresh (fun j => he j.1)] with x hVF hνx hε
  intro pads B Z hZ ψ η d₀ Y q ρ H W χ s w r Q hB hq0 hq1 hρ0 hρ1 hH hW hη hψ hχ
    hdist hd hz hbox hQ hroot
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 1 ≤ 2/Real.log 2 := by
    apply (le_div_iff₀ hlog2).mpr
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hV (j) : 0 < bandReciprocalMass (markedLogPowerBand (e j) x) :=
    (half_pos hlog2).trans_le (hVF j)
  have hVC (j) : (bandReciprocalMass (markedLogPowerBand (e j) x))⁻¹ ≤ 2/Real.log 2 := by
    calc
      _ = 1/bandReciprocalMass (markedLogPowerBand (e j) x) := (one_div _).symm
      _ ≤ 1/(Real.log 2/2) := one_div_le_one_div_of_le (half_pos hlog2) (hVF j)
      _ = _ := by rw [div_div_eq_mul_div]; ring
  have hν : ∀ j p, 0 ≤ markedRawActualPrimeAtom e q x j p := by
    intro j p
    rw [markedRawActualPrimeAtom_eq_tilted]
    exact (hνx q hq0 hq1 j _).1
  have hrow := markedDirtyRawEdge_delta_row_le_counted_expectation (markedRawActualPrimeAtom e q x)
    (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) hν hV hC hVC hZ ψ η d₀ Y hρ0 hρ1.le hH hW
    hη hψ χ hχ s I jstar hstar Q hQ
  have hsum := markedDirtyActualFresh_expectation_eq eFresh q x
    (fun T => markedRawDirtyGoodChoiceMass s.2.1 s.2.2 jstar (I.erase jstar) Z hZ s.1.1 T Q ρ (fun _ _ _ => 0))
  have hAtom : markedRawActualPrimeAtom eFresh q x =
      (fun j : ↥(Finset.univ \ I) => markedRawActualPrimeAtom e q x j.1) := rfl
  rw [hAtom] at hsum
  erw [hsum] at hrow
  have hI : (I.erase jstar).card+1 ≤ Fintype.card J :=
    (Finset.card_erase_add_one hstar).le.trans (Finset.card_le_card (Finset.subset_univ I))
  have hR : Fintype.card ↥(Finset.univ \ I) ≤ Fintype.card J := by
    simpa only [Fintype.card_coe,Finset.card_univ] using Finset.card_le_card (Finset.subset_univ (Finset.univ \ I))
  have hcount := hε (pads+1) B s.2.1 s.2.2 jstar (I.erase jstar) Z hZ s.1.1 w Q r q ρ (fun _ _ _ => 0)
    (Nat.succ_pos pads) hB hI hR hdist hd hz hbox hq0 hq1 hρ0 hρ1 hroot
  exact hrow.trans ((mul_le_mul_of_nonneg_left hcount (by positivity)).trans_eq
    (by unfold markedDirtyActualRowConstant; push_cast; ring))

end ArtinMatthews
