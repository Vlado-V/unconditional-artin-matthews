module

public import ArtinMatthews.MarkedPhysicalEndpointNormBox
public import ArtinMatthews.MarkedMajorTypeIISupportedCoefficient


set_option backward.privateInPublic true
@[expose] public section

/-! The original centered Type-II coefficient with its original support,
and the original beta coefficient restricted to its finite support. The
endpoint norm exponent is independent of K and the growing list length. -/
noncomputable section
open Filter
open scoped BigOperators
namespace ArtinMatthews

def markedPhysicalRestrictedBeta (S : Finset ℕ) (β : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n ∈ S then β n else 0

theorem markedPhysicalRestrictedBeta_norm_sum (S T : Finset ℕ) (β : ℕ → ℂ) :
    (∑ n ∈ T, ‖markedPhysicalRestrictedBeta S β n‖ ^ 2) =
      ∑ n ∈ T ∩ S, ‖β n‖ ^ 2 := by
  classical
  rw [← Finset.filter_mem_eq_inter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : n ∈ S <;> simp [markedPhysicalRestrictedBeta, hn]

theorem markedPhysicalRestrictedBeta_bound (S : Finset ℕ) (β : ℕ → ℂ)
    {Cβ : ℝ} (hCβ : 0 ≤ Cβ) (hβ : ∀ n ∈ S, ‖β n‖ ≤ Cβ) (n : ℕ) :
    ‖markedPhysicalRestrictedBeta S β n‖ ≤ Cβ := by
  classical
  by_cases hn : n ∈ S
  · simpa only [markedPhysicalRestrictedBeta, ite_eq_left hn] using hβ n hn
  · simpa only [markedPhysicalRestrictedBeta, ite_eq_right hn, norm_zero] using hCβ

theorem markedPhysicalEndpointVector_norm_le_global {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (M : ℕ) (α β : ℕ → ℂ)
    {Cα Cβ : ℝ} (hCα : 0 ≤ Cα) (hCβ : 0 ≤ Cβ)
    (hα : ∀ n, ‖α n‖ ≤ Cα) (hβ : ∀ n, ‖β n‖ ≤ Cβ) (z : ℤ × ℤ) :
    ‖markedPhysicalEndpointVector P M α β z‖ ≤ Cα*Cβ := by
  classical
  unfold markedPhysicalEndpointVector
  split_ifs
  · rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hα _) (hβ _) (norm_nonneg _) hCα
  · simpa only [norm_zero] using mul_nonneg hCα hCβ

/-- The actual scalar alpha with its original support gives a physical
energy estimate retaining the entire original beta L² sum and support. -/
theorem markedPhysicalEndpointEnergy_actual_typeII {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, 0 < e j) (hinj : Function.Injective e) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop, ∀ (M : ℕ) (Z : Finset (ℤ × ℤ)) (U V : ℝ),
      0 < U → 0 < V →
      (∀ z ∈ Z, U ≤ (z.1 : ℝ) ∧ (z.1 : ℝ) ≤ 16*U ∧
        V ≤ (z.2 : ℝ) ∧ (z.2 : ℝ) ≤ 2*V) →
      ∀ (Sα Sβ : Finset ℕ) (modulation : ℝ) (β : ℕ → ℂ),
      (∀ n ∈ Sα, Real.exp (δ*L) ≤ (n : ℝ)) →
      markedPhysicalEndpointEnergy (fun j => markedLogPowerBand (e j) (Real.exp L)) M Z
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) (Real.exp L)))
        (markedMajorRestrictedCoefficient (Real.exp (L^(6/25:ℝ))) modulation Sα)
        (markedPhysicalRestrictedBeta Sβ β) ≤
        (16*U)*L^4 * ∑ s ∈ (Finset.Ioc 0 ⌊2*V⌋₊) ∩ Sβ, ‖β s‖ ^ 2 := by
  have hmass := Real.tendsto_exp_atTop.eventually
    (eventually_all.mpr (fun j => marked_log_power_band_mass_eventually (he j)))
  filter_upwards [Real.tendsto_exp_atTop.eventually (marked_array_disjoint_eventually e hinj),
    hmass, markedMajorTypeII_supported_alpha δ hδ] with L hdis hm hα
  intro M Z U V hU hV hZ Sα Sβ modulation β hSα
  have hν : ∀ j, 0 < bandReciprocalMass (markedLogPowerBand (e j) (Real.exp L)) :=
    fun j => (by positivity : 0 < Real.log 2 / 2).trans (hm j).1
  have hbound := markedPhysicalEndpointEnergy_box_alpha _
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) hdis M Z hν hU hV hZ
    (markedMajorRestrictedCoefficient (Real.exp (L^(6/25:ℝ))) modulation Sα)
    (markedPhysicalRestrictedBeta Sβ β) (sq_nonneg L) (fun n _ => (hα Sα modulation hSα).1 n)
  simpa only [markedPhysicalRestrictedBeta_norm_sum, ← pow_mul, show 2*2=4 by omega] using hbound

/-- Both Hilbert and pointwise bounds for the actual physical endpoints.
The only beta bound is the original scalar bound on its original finite
support. The exponent `C+2` is independent of bands and list length. -/
theorem markedPhysicalEndpointNorm_actual_typeII {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, 0 < e j) (hinj : Function.Injective e) (δ : ℝ) (hδ : 0 < δ)
    (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (M : ℕ) (Z : Finset (ℤ × ℤ)) (U V : ℝ),
      0 < U → 0 < V →
      (∀ z ∈ Z, U ≤ (z.1 : ℝ) ∧ (z.1 : ℝ) ≤ 16*U ∧
        V ≤ (z.2 : ℝ) ∧ (z.2 : ℝ) ≤ 2*V) →
      ∀ (Sα Sβ : Finset ℕ) (modulation : ℝ) (β : ℕ → ℂ),
      (∀ n ∈ Sα, Real.exp (δ*L) ≤ (n : ℝ)) → (∀ n ∈ Sβ, ‖β n‖ ≤ L^C) →
      (markedPhysicalEndpointNorm (fun j => markedLogPowerBand (e j) (Real.exp L)) M Z
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) (Real.exp L)))
        (markedMajorRestrictedCoefficient (Real.exp (L^(6/25:ℝ))) modulation Sα)
        (markedPhysicalRestrictedBeta Sβ β) ≤ Real.sqrt (32*U*V)*L^(C+2)) ∧
      (∀ z : ℤ × ℤ, ‖markedPhysicalEndpointVector (fun j => markedLogPowerBand (e j) (Real.exp L)) M
        (markedMajorRestrictedCoefficient (Real.exp (L^(6/25:ℝ))) modulation Sα)
        (markedPhysicalRestrictedBeta Sβ β) z‖ ≤ L^(C+2)) := by
  have hmass := Real.tendsto_exp_atTop.eventually
    (eventually_all.mpr (fun j => marked_log_power_band_mass_eventually (he j)))
  filter_upwards [Real.tendsto_exp_atTop.eventually (marked_array_disjoint_eventually e hinj),
    hmass, markedMajorTypeII_supported_alpha δ hδ, eventually_gt_atTop (0 : ℝ)] with L hdis hm hα hL
  intro M Z U V hU hV hZ Sα Sβ modulation β hSα hβ
  have hν : ∀ j, 0 < bandReciprocalMass (markedLogPowerBand (e j) (Real.exp L)) :=
    fun j => (by positivity : 0 < Real.log 2 / 2).trans (hm j).1
  have hβ' := markedPhysicalRestrictedBeta_bound Sβ β (Real.rpow_nonneg hL.le C) hβ
  have hpow : L^2 * L^C = L^(C+2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hL]
    congr 1
    ring
  constructor
  · rw [← hpow]
    exact markedPhysicalEndpointNorm_box _ (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
      hdis M Z hν hU hV hZ _ _ (sq_nonneg L) (Real.rpow_nonneg hL.le C)
      (fun n _ => (hα Sα modulation hSα).1 n) (fun n _ => hβ' n)
  · intro z
    rw [← hpow]
    exact markedPhysicalEndpointVector_norm_le_global _ M _ _ (sq_nonneg L) (Real.rpow_nonneg hL.le C)
      (hα Sα modulation hSα).1 hβ' z

/-- The same coefficient-sensitive bound in the original x/log(x) variables. -/
theorem markedPhysicalEndpointEnergy_actual_typeII_log {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, 0 < e j) (hinj : Function.Injective e) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, ∀ (M : ℕ) (Z : Finset (ℤ × ℤ)) (U V : ℝ),
      0 < U → 0 < V →
      (∀ z ∈ Z, U ≤ (z.1 : ℝ) ∧ (z.1 : ℝ) ≤ 16*U ∧
        V ≤ (z.2 : ℝ) ∧ (z.2 : ℝ) ≤ 2*V) →
      ∀ (Sα Sβ : Finset ℕ) (modulation : ℝ) (β : ℕ → ℂ),
      (∀ n ∈ Sα, x^δ ≤ (n : ℝ)) →
      markedPhysicalEndpointEnergy (fun j => markedLogPowerBand (e j) x) M Z
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
        (markedMajorRestrictedCoefficient (Real.exp ((Real.log x)^(6/25:ℝ))) modulation Sα)
        (markedPhysicalRestrictedBeta Sβ β) ≤
        (16*U)*(Real.log x)^4 * ∑ s ∈ (Finset.Ioc 0 ⌊2*V⌋₊) ∩ Sβ, ‖β s‖ ^ 2 := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (markedPhysicalEndpointEnergy_actual_typeII e he hinj δ hδ),
    eventually_gt_atTop (0 : ℝ)] with x hx hxpos
  have hexp : Real.exp (δ * Real.log x) = x^δ := by
    rw [Real.rpow_def_of_pos hxpos, mul_comm]
  simpa only [Real.exp_log hxpos, hexp] using hx

/-- The literal physical endpoint norms with L=log x and the actual prime
bands at x; the exponent remains independent of K and M. -/
theorem markedPhysicalEndpointNorm_actual_typeII_log {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, 0 < e j) (hinj : Function.Injective e) (δ : ℝ) (hδ : 0 < δ)
    (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ (M : ℕ) (Z : Finset (ℤ × ℤ)) (U V : ℝ),
      0 < U → 0 < V →
      (∀ z ∈ Z, U ≤ (z.1 : ℝ) ∧ (z.1 : ℝ) ≤ 16*U ∧
        V ≤ (z.2 : ℝ) ∧ (z.2 : ℝ) ≤ 2*V) →
      ∀ (Sα Sβ : Finset ℕ) (modulation : ℝ) (β : ℕ → ℂ),
      (∀ n ∈ Sα, x^δ ≤ (n : ℝ)) → (∀ n ∈ Sβ, ‖β n‖ ≤ (Real.log x)^C) →
      (markedPhysicalEndpointNorm (fun j => markedLogPowerBand (e j) x) M Z
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
        (markedMajorRestrictedCoefficient (Real.exp ((Real.log x)^(6/25:ℝ))) modulation Sα)
        (markedPhysicalRestrictedBeta Sβ β) ≤ Real.sqrt (32*U*V)*(Real.log x)^(C+2)) ∧
      (∀ z : ℤ × ℤ, ‖markedPhysicalEndpointVector (fun j => markedLogPowerBand (e j) x) M
        (markedMajorRestrictedCoefficient (Real.exp ((Real.log x)^(6/25:ℝ))) modulation Sα)
        (markedPhysicalRestrictedBeta Sβ β) z‖ ≤ (Real.log x)^(C+2)) := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (markedPhysicalEndpointNorm_actual_typeII e he hinj δ hδ C),
    eventually_gt_atTop (0 : ℝ)] with x hx hxpos
  have hexp : Real.exp (δ * Real.log x) = x^δ := by
    rw [Real.rpow_def_of_pos hxpos, mul_comm]
  simpa only [Real.exp_log hxpos, hexp] using hx

end ArtinMatthews
