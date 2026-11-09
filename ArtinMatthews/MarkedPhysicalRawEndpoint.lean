module

public import ArtinMatthews.MarkedPhysicalRawZero
public import ArtinMatthews.MarkedRawGoodProjection
public import ArtinMatthews.MarkedMinorArcRawEdgeSlotTranspose


set_option backward.privateInPublic true
@[expose] public section

/-! Physical endpoints retain their exact counting mass under empty-memory
transport. Their slot symmetry and zero extensions are proved explicitly. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysicalStateCondition_slots {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (z : ℤ × ℤ) (a : MarkedPhysicalMarking P M) (σ : J → Equiv.Perm (Fin M)) :
    MarkedPhysicalStateCondition z (fun j k => a j (σ j k)) ↔ MarkedPhysicalStateCondition z a := by
  constructor
  · rintro ⟨hz,hi,hd⟩
    refine ⟨hz,?_,?_⟩
    · intro j k l hkl
      apply (σ j).symm.injective
      apply hi j
      simpa only [Equiv.apply_symm_apply] using hkl
    · intro j k
      simpa only [Equiv.apply_symm_apply] using hd j ((σ j).symm k)
  · rintro ⟨hz,hi,hd⟩
    exact ⟨hz,fun j => (hi j).comp (σ j).injective,fun j k => hd j (σ j k)⟩

theorem markedPhysicalRawEndpoint_slots {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime)
    (M : ℕ) (Z : Finset (ℤ × ℤ)) (α β : ℕ → ℂ)
    (σ : J → Equiv.Perm (Fin M))
    (s : MarkedRawState (fun j => markedRawPrimeBand (P j)) M 0 Z) :
    markedPhysicalRawEndpoint P hP M Z α β (markedRawSlotEquiv σ s) =
      markedPhysicalRawEndpoint P hP M Z α β s := by
  have hmark : markedPhysicalMarkingEquiv P hP M (markedRawSlotEquiv σ s).2.1 =
      fun j k => (markedPhysicalMarkingEquiv P hP M s.2.1) j (σ j k) := rfl
  have hc := markedPhysicalStateCondition_slots s.1.1 (markedPhysicalMarkingEquiv P hP M s.2.1) σ
  unfold markedPhysicalRawEndpoint markedPhysicalRawZeroVector markedPhysicalStateExtend
  change (if h : MarkedPhysicalStateCondition s.1.1
      (markedPhysicalMarkingEquiv P hP M (markedRawSlotEquiv σ s).2.1) then
        markedPhysicalEndpointVector P M α β s.1.1 else 0) =
    (if h : MarkedPhysicalStateCondition s.1.1 (markedPhysicalMarkingEquiv P hP M s.2.1) then
        markedPhysicalEndpointVector P M α β s.1.1 else 0)
  rw [hmark]
  simp only [hc]

theorem markedPhysicalRawEndpoint_slotAverage {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime)
    (M : ℕ) (Z : Finset (ℤ × ℤ)) (α β : ℕ → ℂ) :
    markedRawSlotAverage (markedPhysicalRawEndpoint P hP M Z α β) =
      markedPhysicalRawEndpoint P hP M Z α β :=
  markedRawSlotAverage_eq_of_invariant _ (markedPhysicalRawEndpoint_slots P hP M Z α β)

theorem markedPhysicalRawZeroVector_goodProjection {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime)
    (M : ℕ) (Z : Finset (ℤ × ℤ))
    (G : MarkedRawState (fun j => markedRawPrimeBand (P j)) M 0 Z → Prop)
    (f : MarkedPhysicalState P M Z → ℂ) :
    markedPhysicalRawZeroVector P hP M Z
        (markedPhysicalGoodVector (fun s => G (markedPhysicalStateToRaw P hP M Z s)) f) =
      markedRawGoodProjection G (markedPhysicalRawZeroVector P hP M Z f) := by
  funext s
  let t := markedPhysicalRawZeroEquiv P hP M Z s
  have ht : (markedPhysicalRawZeroEquiv P hP M Z).symm t = s :=
    Equiv.symm_apply_apply _ s
  by_cases hc : MarkedPhysicalStateCondition t.1.1 t.2
  · have he : markedPhysicalStateToRaw P hP M Z ⟨t,hc⟩ = s := ht
    simp only [markedPhysicalRawZeroVector,markedPhysicalStateExtend,show markedPhysicalRawZeroEquiv P hP M Z s=t from rfl,
      dite_eq_left hc,markedPhysicalGoodVector,he,markedRawGoodProjection]
  · simp only [markedPhysicalRawZeroVector,markedPhysicalStateExtend,show markedPhysicalRawZeroEquiv P hP M Z s=t from rfl,
      dite_eq_right hc,markedRawGoodProjection,ite_self]

theorem markedPhysicalRawEndpoint_energy_actual_typeII_log
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,0 < e j) (hinj : Function.Injective e) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, ∀ (M : ℕ) (Z : Finset (ℤ × ℤ)) (U V : ℝ),
      0 < U → 0 < V →
      (∀ z ∈ Z,U ≤ (z.1 : ℝ) ∧ (z.1 : ℝ) ≤ 16*U ∧ V ≤ (z.2 : ℝ) ∧ (z.2 : ℝ) ≤ 2*V) →
      ∀ (Sα Sβ : Finset ℕ) (modulation : ℝ) (β : ℕ → ℂ),
      (∀ n ∈ Sα,x^δ ≤ (n : ℝ)) →
      (∑ s : MarkedRawState (markedRawActualPrimeBand e x) M 0 Z,
        markedRawStateMass (fun j _ => (bandReciprocalMass (markedLogPowerBand (e j) x))⁻¹) s *
          ‖markedPhysicalRawEndpoint (fun j => markedLogPowerBand (e j) x)
            (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) M Z
            (markedMajorRestrictedCoefficient (Real.exp ((Real.log x)^(6/25:ℝ))) modulation Sα)
            (markedPhysicalRestrictedBeta Sβ β) s‖^2) ≤
        (16*U)*(Real.log x)^4 * ∑ s ∈ (Finset.Ioc 0 ⌊2*V⌋₊) ∩ Sβ,‖β s‖^2 := by
  filter_upwards [markedPhysicalEndpointEnergy_actual_typeII_log e he hinj δ hδ] with x hx
  intro M Z U V hU hV hbox Sα Sβ modulation β hSα
  exact (markedPhysicalRawEndpoint_energy (fun j => markedLogPowerBand (e j) x)
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
    (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) M Z
    (markedMajorRestrictedCoefficient (Real.exp ((Real.log x)^(6/25:ℝ))) modulation Sα)
    (markedPhysicalRestrictedBeta Sβ β)).trans_le
      (hx M Z U V hU hV hbox Sα Sβ modulation β hSα)

end ArtinMatthews
