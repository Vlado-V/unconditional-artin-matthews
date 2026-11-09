module

public import ArtinMatthews.MarkedPhysicalEndpointDamping


set_option backward.privateInPublic true
@[expose] public section

/-! Instantiation on the literal growing prime bands. The normalization is
uniform over every full-list length, in particular the actual growing M. -/
noncomputable section
open Filter
open scoped BigOperators ComplexConjugate
namespace ArtinMatthews
attribute [local instance] Classical.propDecidable

theorem markedPhysical_actual_normalization_eventually {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, 0 < e j) :
    ∀ᶠ x : ℝ in atTop, ∀ M : ℕ,
      (∑ a : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) M,
        if MarkedPhysicalMarkingDistinct a then
          markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) M *
            markedPhysicalReciprocalProduct a else 0) ≤ 1 := by
  have hmass := eventually_all.mpr (fun j => marked_log_power_band_mass_eventually (he j))
  filter_upwards [hmass] with x hx
  intro M
  exact markedPhysicalMarking_distinct_normalized_sum_le_one _ M
    (fun j => (by positivity : 0 < Real.log 2 / 2).trans (hx j).1)

/-- Actual band support is recovered exactly from the original full lists
for every growing list length and every finite primitive-position set. -/
theorem markedPhysical_actual_state_support_eventually {J : Type*} [Fintype J]
    (e : J → ℝ) (hinj : Function.Injective e) :
    ∀ᶠ x : ℝ in atTop, ∀ (M : ℕ) (Z : Finset (ℤ × ℤ))
      (s : MarkedPhysicalState (fun j => markedLogPowerBand (e j) x) M Z),
      MarkedPhysicalEndpointSupport (fun j => markedLogPowerBand (e j) x) M s.1.1.1.1.natAbs ↔
        MarkedPhysicalBandRough (fun j => markedLogPowerBand (e j) x)
          (s.1.1.1.1.natAbs / markedPhysicalMarkingProduct s.1.2) := by
  filter_upwards [marked_array_disjoint_eventually e hinj] with x hx
  intro M Z s
  exact markedPhysicalState_support_iff _ (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) hx M Z s

/-- The original four scalar coefficients are recovered on the actual
bands, not on an abstract family satisfying a source-identity hypothesis. -/
theorem markedPhysical_actual_pairing_eventually {J : Type*} [Fintype J]
    (e : J → ℝ) (hinj : Function.Injective e) :
    ∀ᶠ x : ℝ in atTop, ∀ (M : ℕ)
      (b a : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) M),
      MarkedPhysicalMarkingDistinct b → MarkedPhysicalMarkingDistinct a →
      ∀ m r : ℕ, MarkedPhysicalBandRough (fun j => markedLogPowerBand (e j) x) m →
        MarkedPhysicalBandRough (fun j => markedLogPowerBand (e j) x) r →
      ∀ (s n : ℕ) (α β : ℕ → ℂ),
      conj (markedPhysicalEndpointVector (fun j => markedLogPowerBand (e j) x) M α β
        (markedPhysicalLift (markedPhysicalMarkingProduct b) m s)) *
      markedPhysicalEndpointVector (fun j => markedLogPowerBand (e j) x) M α β
        (markedPhysicalLift (markedPhysicalMarkingProduct a) r n) =
        α m * conj (α r) * β n * conj (β s) := by
  filter_upwards [marked_array_disjoint_eventually e hinj] with x hx
  intro M b a hb ha m r hm hr s n α β
  exact markedPhysicalEndpoint_pairing_lift (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
    hx b a hb ha hm hr s n α β

end ArtinMatthews
