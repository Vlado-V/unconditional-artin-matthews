module

public import ArtinMatthews.MarkedMinorArcDirtyGoodSignedActual
public import ArtinMatthews.MarkedMinorArcDirtyCombinedDecay


set_option backward.privateInPublic true
@[expose] public section

/-! Sum every nonempty promoted set and every store pattern. The actual
beta and first-good cutoffs supply all arithmetic row conditions. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedDirtyPromotedDeltaConstant (K : ℕ) (ρ H W v₀ L : ℝ) : ℝ :=
  (2:ℝ)^K*L*(v₀^K*markedDirtyActualRowConstant K ρ H W)

def markedDirtyPromotedMajorConstant (K : ℕ) (v₀ H W c T A L : ℝ) : ℝ :=
  (2:ℝ)^K*L*(2*markedDirtyMajorActualConstant K v₀ H W c T A)

theorem markedDirty_good_promoted_row_envelope
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (hinj : Function.Injective e)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (v₀ c T A H W ρ L A₀ : ℝ)
    (hv₀ : 1 ≤ v₀) (hc : 0 < c) (hT : 0 ≤ T) (hH : 0 ≤ H) (hW : 0 ≤ W)
    (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1) (hL : 0 ≤ L)
    (hη : ∀ t,‖η t‖ ≤ H) (hψ : ∀ t,‖ψ t‖ ≤ W) (hsupp : Function.support ψ ⊆ Set.Icc (-A) A) :
    ∀ᶠ x : ℝ in atTop, ∀ (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
      (r d₀ Y q : ℝ) (w : Z → ℤ × ℤ)
      (χ : MarkedRawState (markedRawActualPrimeBand e x) (markedPadSlots x) (markedDirtyMemoryCutoff x) Z → ℂ)
      (s : MarkedRawState (markedRawActualPrimeBand e x) (markedPadSlots x) (markedDirtyMemoryCutoff x) Z)
      (modifier : (σ : J → Equiv.Perm (Fin (markedPadSlots x))) → MarkedRawEdgeChoice hZ (markedRawSlotEquiv σ s) → ℂ),
      Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y → 0 ≤ q → q ≤ 1 →
      (∀ z,markedMinorIntegerDet z.1 (w z)=1) →
      (∀ z ∈ Z,c ≤ |markedMinorIntegerTau r z| ∧ |markedMinorIntegerTau r z| ≤ T) →
      (∀ z v : Z,|markedMinorIntegerTau r v.1/markedMinorIntegerTau r z.1| ≤ 16) →
      (∀ s,‖χ s‖ ≤ 1) → (∀ σ c,‖modifier σ c‖ ≤ L) →
      markedDirtyPromotedWeightedRow (markedRawActualPrimeAtom e q x)
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) hZ ψ η r d₀ Y ((Real.log x)^A₀) ρ v₀ w
        (markedRawDirtySecondGoodCutoff e x r w χ) s modifier ≤
      markedDirtyCombinedEnvelope (markedDirtyPromotedDeltaConstant (Fintype.card J) ρ H W v₀ L)
        (markedDirtyPromotedMajorConstant (Fintype.card J) v₀ H W c T A L) (Fintype.card J) A₀ x := by
  classical
  have hall := eventually_all.mpr (fun I : {I : Finset J // I.Nonempty} =>
    markedDirty_good_signed_fixed_row_eventually e he hinj I.1 I.2)
  filter_upwards [hall,Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx hlog
  intro Z hZ r d₀ Y q w χ s modifier hYexp hq₀ hq₁ hw hτ hbox hχ hmodifier
  have hlogpos : 0 < Real.log x := zero_lt_one.trans_le hlog
  have hY : 1 ≤ Y := (show 1 ≤ Real.exp ((Real.log x)^(1/10:ℝ)) by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (Real.rpow_nonneg hlogpos.le (1/10:ℝ))).trans hYexp
  have hYpos : 0 < Y := zero_lt_one.trans_le hY
  have hQ : 0 ≤ (Real.log x)^A₀ := Real.rpow_nonneg hlogpos.le _
  have hB : 1 ≤ markedDirtyMemoryCutoff x := by
    have hsq : (1:ℝ) ≤ (Real.log x)^2 := one_le_pow₀ hlog
    have hceil : (Real.log x)^2 ≤ (markedDirtyMemoryCutoff x:ℝ) := Nat.le_ceil _
    exact_mod_cast hsq.trans hceil
  let D := v₀^(Fintype.card J)*markedDirtyActualRowConstant (Fintype.card J) ρ H W
  let M := markedDirtyMajorActualConstant (Fintype.card J) v₀ H W c T A
  have hD : 0 ≤ D := markedDirtyActualWeightedConstant_nonneg _ hv₀ hW
  have hM : 0 ≤ M := markedDirtyMajorActualConstant_nonneg _ hv₀ hW
  let Rd := D*((markedDirtyMemoryCutoff x:ℝ)*(markedPadSlots x:ℝ)⁻¹^(Fintype.card J)+
    (markedDirtyMemoryCutoff x:ℝ)^(Fintype.card J)*Real.exp (-((Real.log x)^(1/10:ℝ))/4))
  let Rm := M*(markedDirtyMemoryCutoff x+1:ℝ)^(Fintype.card J)*((Real.log x)^A₀)^3*
    (Real.exp (-((Real.log x)^(1/10:ℝ)))+Y^(-1/10:ℝ))
  have hR : 0 ≤ L*(Rd+Rm) := by
    dsimp [Rd,Rm]
    positivity
  have hsum := markedDirtyPromotedWeightedRow_le_of_fixed (markedRawActualPrimeAtom e q x)
    (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) hZ ψ η r d₀ Y ((Real.log x)^A₀) ρ v₀ w
    (markedRawDirtySecondGoodCutoff e x r w χ) s modifier hR (fun I hI => by
      simpa only [D,Rd,Rm,M,markedPadSlots,Nat.cast_add,Nat.cast_one] using
        hx ⟨I,hI⟩ ⌊(Real.log x)^(1/100:ℝ)⌋₊ (markedDirtyMemoryCutoff x) Z hZ ψ η
        r d₀ Y ((Real.log x)^A₀) q ρ H W v₀ c T A L w χ s modifier
        hB hY hQ hq₀ hq₁ hρ₀ hρ₁ hH hW hv₀ hc hT hL hη hψ hsupp hw hτ hbox hχ hmodifier)
  apply hsum.trans
  have htail := markedDirtyMajor_tail_le hlogpos.le hYexp
  dsimp [Rd,Rm]
  calc
    _ ≤ (2:ℝ)^(Fintype.card J)*(L*(D*((markedDirtyMemoryCutoff x:ℝ)*(markedPadSlots x:ℝ)⁻¹^(Fintype.card J)+
        (markedDirtyMemoryCutoff x:ℝ)^(Fintype.card J)*Real.exp (-((Real.log x)^(1/10:ℝ))/4))+
        M*(markedDirtyMemoryCutoff x+1:ℝ)^(Fintype.card J)*((Real.log x)^A₀)^3*
          (2*Real.exp (-(1/10:ℝ)*(Real.log x)^(1/10:ℝ))))) := by
      gcongr
    _ = _ := by
      unfold markedDirtyCombinedEnvelope markedDirtyScalarEpsilon markedDirtyMajorEnvelope
        markedDirtyPromotedDeltaConstant markedDirtyPromotedMajorConstant
      dsimp [D,M]
      ring

end
end ArtinMatthews
