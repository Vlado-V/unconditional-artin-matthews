module

public import ArtinMatthews.MarkedMinorArcDirtyMajorChoiceSym
public import ArtinMatthews.MarkedMinorArcDirtyMajorActualTransfer


set_option backward.privateInPublic true
@[expose] public section

/-! Actual log-prime weights and prime lower bounds in the literal
source-symmetrized, v0-weighted major comparison row. -/
noncomputable section
namespace ArtinMatthews

open Filter
open scoped BigOperators Topology

def markedDirtyMajorActualConstant (groups : ℕ) (v₀ H W c Bτ K : ℝ) : ℝ :=
  1200*(max 1 (max (Bτ/c) K))^2*(2/Real.log 2)^groups*H^2*W*v₀^groups*(4:ℝ)^groups

set_option backward.isDefEq.respectTransparency false in
theorem markedDirtyMajor_actual_weighted_row_eventually {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) (I : Finset J) (jstar : I) :
    ∀ᶠ x : ℝ in atTop, ∀ (pads B : ℕ) (Z : Finset (ℤ × ℤ))
      (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (η ψ : ℝ → ℂ) (r d₀ Y Q q ρ v₀ c Bτ K H W : ℝ)
      (w : Z → ℤ × ℤ) (χ : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ)
      (s : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z),
      1 ≤ Y → 0 ≤ Q → 0 ≤ q → q ≤ 1 → 0 < c → 0 ≤ Bτ →
      0 ≤ ρ → ρ ≤ 1 → 1 ≤ v₀ → 0 ≤ H → 0 ≤ W →
      (∀ t, ‖η t‖ ≤ H) → (∀ t, ‖ψ t‖ ≤ W) → Function.support ψ ⊆ Set.Icc (-K) K →
      (∀ z, markedMinorIntegerDet z.1 (w z)=1) →
      (∀ z ∈ Z, c ≤ |markedMinorIntegerTau r z| ∧ |markedMinorIntegerTau r z| ≤ Bτ) →
      (∀ s, ‖χ s‖ ≤ 1) →
      markedDirtyMajorSymWeightedRow (markedRawActualPrimeAtom e q x)
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) hZ η ψ r d₀ Y Q ρ v₀ w χ s I ≤
        markedDirtyMajorActualConstant (Fintype.card J) v₀ H W c Bτ K*(B+1:ℝ)^(Fintype.card J)*Q^3*
          (Real.exp (-((Real.log x)^(1/10:ℝ)))+Y^(-1/10:ℝ)) := by
  classical
  let eFresh : ↥(Finset.univ \ I) → ℝ := fun j => e j.1
  filter_upwards [markedDirty_actual_band_transfer_eventually e he,
    markedDirty_actual_band_transfer_eventually eFresh (fun j => he j.1),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hfull hfresh hlog
  intro pads B Z hZ η ψ r d₀ Y Q q ρ v₀ c Bτ K H W w χ s hY hQ hq0 hq1 hc hBτ hρ₀ hρ₁ hv₀ hH hW
    hη hψ hsupp hw hτ hχ
  have hf := hfull q hq0 hq1
  have hs := hfresh q hq0 hq1
  have hmass : (∑ fresh : (j : ↥(Finset.univ \ I)) → ↥(markedRawActualPrimeBand e x j.1),
      finiteProductMass (fun j : ↥(Finset.univ \ I) => markedRawActualPrimeAtom e q x j.1) fresh) ≤
      (2:ℝ)^(Fintype.card J) := by
    have hh : (∑ fresh : (j : ↥(Finset.univ \ I)) → ↥(markedRawActualPrimeBand e x j.1),
        finiteProductMass (fun j : ↥(Finset.univ \ I) => markedRawActualPrimeAtom e q x j.1) fresh) ≤
        (2:ℝ)^(Fintype.card ↥(Finset.univ \ I)) := by
      have hAtom : markedRawActualPrimeAtom eFresh q x=
          (fun j : ↥(Finset.univ \ I) => markedRawActualPrimeAtom e q x j.1) := rfl
      erw [← hAtom]
      exact hs.2.2
    exact hh.trans (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2)
      (by simpa only [Fintype.card_coe,Finset.card_univ] using Finset.card_le_card (Finset.subset_univ (Finset.univ \ I))))
  have hp : ∀ k : Fin (s.2.2.1.1 jstar.1:ℕ), Real.exp ((Real.log x)^(1/10:ℝ)) ≤ ((s.2.2.2 jstar.1 k).1.1:ℕ) := by
    intro k
    apply marked_band_common_lower (he jstar.1) hlog
    exact (mem_markedRawPrimeBand _ _).mp (s.2.2.2 jstar.1 k).1.2
  have hrow := markedDirtyMajorSymWeightedRow_le (markedRawActualPrimeAtom e q x)
    (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) hf.1 (fun j => (hf.2.1 j).1)
    markedDirty_transfer_constant_one_le (fun j => (hf.2.1 j).2) hZ η ψ r d₀ Y Q ρ v₀ hY hQ hc hBτ
    (Real.exp_pos _) hρ₀ hρ₁ hv₀ hH hW hη hψ hsupp w hw hτ χ hχ s I jstar hp
  apply hrow.trans
  calc
    _ ≤ v₀^(Fintype.card J)*1200*(max 1 (max (Bτ/c) K))^2*(2/Real.log 2)^(Fintype.card J)*H^2*W*
        (2:ℝ)^(Fintype.card J)*(B+1:ℝ)^(Fintype.card J)*(2:ℝ)^(Fintype.card J)*Q^3*
          (1/Real.exp ((Real.log x)^(1/10:ℝ))+Y^(-1/10:ℝ)) := by
      gcongr
    _ = _ := by
      unfold markedDirtyMajorActualConstant
      simp only [one_div,Real.exp_neg]
      rw [show (4:ℝ)^(Fintype.card J)=(2:ℝ)^(Fintype.card J)*(2:ℝ)^(Fintype.card J) by rw [← mul_pow]; norm_num]
      ring

end ArtinMatthews
