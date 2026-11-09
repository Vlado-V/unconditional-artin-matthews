module

public import ArtinMatthews.MarkedRawGoodRootMeasure
public import ArtinMatthews.MarkedPhysicalEndpointNormActual


set_option backward.privateInPublic true
@[expose] public section

/-! Conditional source-root averaging of the actual physical endpoint.
The vector is fixed independently of the root parameter. These integrated
energies do not give a uniform operator norm for bad-state projections. -/
namespace ArtinMatthews
noncomputable section
open Filter MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedFixedBadRootEnergy_integral {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (f : Ω → ℂ) (bad : Ω → Set (AddCircle (1:ℝ)))
    (hbad : ∀ s,MeasurableSet (bad s)) :
    (∫ θ : AddCircle (1:ℝ),∑ s,μ s*‖if θ ∈ bad s then f s else 0‖^2) =
      ∑ s,μ s*‖f s‖^2*volume.real (bad s) := by
  have he (s : Ω) : (fun θ : AddCircle (1:ℝ) => μ s*‖if θ ∈ bad s then f s else 0‖^2) =
      (bad s).indicator (fun _ => μ s*‖f s‖^2) := by
    funext θ
    by_cases h : θ ∈ bad s <;> simp [h]
  have hi (s : Ω) : Integrable (fun θ : AddCircle (1:ℝ) =>
      μ s*‖if θ ∈ bad s then f s else 0‖^2) volume := by
    rw [he]
    exact (integrable_const _).indicator (hbad s)
  rw [integral_finsetSum _ (fun s _ => hi s)]
  apply Finset.sum_congr rfl
  intro s _
  rw [he,integral_indicator_const _ (hbad s)]
  ring

theorem markedFixedBadRootEnergy_integral_le {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (hμ : ∀ s,0 ≤ μ s) (f : Ω → ℂ)
    (bad : Ω → Set (AddCircle (1:ℝ))) (hbad : ∀ s,MeasurableSet (bad s))
    {δ : ℝ} (hδ : ∀ s,volume.real (bad s) ≤ δ) :
    (∫ θ : AddCircle (1:ℝ),∑ s,μ s*‖if θ ∈ bad s then f s else 0‖^2) ≤
      δ*∑ s,μ s*‖f s‖^2 := by
  rw [markedFixedBadRootEnergy_integral μ f bad hbad,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  exact (mul_le_mul_of_nonneg_left (hδ s) (mul_nonneg (hμ s) (sq_nonneg _))).trans_eq (by ring)

def markedPhysicalRootBadSet {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x d₀ Y : ℝ) {Z : Finset (ℤ × ℤ)}
    (s : MarkedPhysicalState (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) Z) :
    Set (AddCircle (1:ℝ)) :=
  markedRawBadRootSet e x d₀ Y
    ((markedPhysicalMarkingEquiv (fun j => markedLogPowerBand (e j) x)
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) (markedPadSlots x)).symm s.1.2)

def markedPhysicalRootBadVector {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x d₀ Y : ℝ) {Z : Finset (ℤ × ℤ)} (α β : ℕ → ℂ)
    (θ : AddCircle (1:ℝ))
    (s : MarkedPhysicalState (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) Z) : ℂ :=
  if θ ∈ markedPhysicalRootBadSet e x d₀ Y s then
    markedPhysicalEndpointVector (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) α β s.1.1.1
  else 0

theorem markedPhysicalRootBadVector_actual_energy {J : Type*} [Fintype J] [decJ : DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (hinj : Function.Injective e) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop,∀ (d₀ Y : ℝ) (Z : Finset (ℤ × ℤ)) (α β : ℕ → ℂ),
      Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y →
      (∫ θ : AddCircle (1:ℝ),
        ∑ s : MarkedPhysicalState (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) Z,
          markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x) *
            ‖markedPhysicalRootBadVector e x d₀ Y α β θ s‖^2) ≤
        (Real.log x)^(-A)*markedPhysicalEndpointEnergy (fun j => markedLogPowerBand (e j) x)
          (markedPadSlots x) Z (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) α β := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  have hband := eventually_all.mpr (fun j => marked_log_power_band_mass_eventually
    (show 0 < e j by linarith [he j]))
  filter_upwards [markedRawBadRootSet_log_saving e he hinj A,hband] with x hx hb
  intro d₀ Y Z α β hY
  exact markedFixedBadRootEnergy_integral_le
    (Ω := MarkedPhysicalState (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) Z)
    (fun _ => markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x))
    (fun _ => markedPhysicalMass_nonneg _ _ (fun j => (by positivity : 0 < Real.log 2/2).le.trans (hb j).1.le))
    (fun s => markedPhysicalEndpointVector (fun j => markedLogPowerBand (e j) x)
      (markedPadSlots x) α β s.1.1.1)
    (markedPhysicalRootBadSet e x d₀ Y)
    (fun s => markedRawBadRootSet_measurable e x d₀ Y _)
    (fun s => hx d₀ Y hY _)

def markedRawRootBadBoundary {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x d₀ Y : ℝ) {B : ℕ} {Z : Finset (ℤ × ℤ)} (z₀ : Z)
    (θ : AddCircle (1:ℝ))
    (s : MarkedRawState (markedRawActualPrimeBand e x) (markedPadSlots x) B Z) : ℂ :=
  if θ ∈ markedRawBadRootSet e x d₀ Y s.2.1 then markedRawBoundary z₀ s else 0

theorem markedRawRootBadBoundary_actual_energy {J : Type*} [Fintype J] [decJ : DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (hinj : Function.Injective e) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop,∀ (q d₀ Y : ℝ) (B : ℕ) (Z : Finset (ℤ × ℤ)) (z₀ : Z),
      0 ≤ q → q ≤ 1 → Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y →
      (∫ θ : AddCircle (1:ℝ),
        ∑ s : MarkedRawState (markedRawActualPrimeBand e x) (markedPadSlots x) B Z,
          markedRawStateMass (markedRawActualPrimeAtom e q x) s *
            ‖markedRawRootBadBoundary e x d₀ Y z₀ θ s‖^2) ≤ 2*(Real.log x)^(-A) := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  filter_upwards [markedRawBadRootSet_log_saving e he hinj A,
    markedRawBoundary_actual_energy_le_two e he,markedRawActualStateMass_nonneg_eventually e he,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (0:ℝ))] with x hx hb hmass hlog
  intro q d₀ Y B Z z₀ hq₀ hq₁ hY
  have h := markedFixedBadRootEnergy_integral_le
    (markedRawStateMass (markedRawActualPrimeAtom e q x)) (hmass q hq₀ hq₁ _ B Z)
    (markedRawBoundary z₀) (fun s => markedRawBadRootSet e x d₀ Y s.2.1)
    (fun s => markedRawBadRootSet_measurable e x d₀ Y s.2.1) (fun s => hx d₀ Y hY s.2.1)
  apply h.trans
  have hpow : 0 ≤ (Real.log x)^(-A) := Real.rpow_nonneg hlog _
  calc
    _ ≤ (Real.log x)^(-A)*2 := mul_le_mul_of_nonneg_left (hb q hq₀ hq₁ B Z z₀) hpow
    _ = _ := by ring

end
end ArtinMatthews
