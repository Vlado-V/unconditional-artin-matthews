module

public import ArtinMatthews.MarkedPhysicalBadHaarLines
public import ArtinMatthews.MarkedPhysicalEdgeIncidence


set_option backward.privateInPublic true
@[expose] public section

/-! The actual two-endpoint prime incidences discharge the finite-line
condition in the positive bad-root Haar estimate. The source is the
literal prefix of the original ordered union marking. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators LinearAlgebra.Projectivization
attribute [local instance] Classical.propDecidable

def markedPhysicalEdgeRootLineEvent {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M : ℕ} (u : MarkedPhysicalMarking P (M+2))
    (hS : Squarefree (markedPhysicalMarkingProduct u))
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod (markedPhysicalMarkingProduct u)))
    (z : ℤ × ℤ) : Prop :=
  ∃ hz : IsCoprime z.1 z.2, markedPhysicalEdgeLineIncidence u hS g z hz

def markedPhysicalEdgeRootAssignedLines {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M : ℕ} (u : MarkedPhysicalMarking P (M+2))
    (z : ℤ × ℤ) : MarkedRootLineTuple (markedPhysicalMarkingProduct u) :=
  if hz : IsCoprime z.1 z.2 then markedPhysicalEdgeAssignedLines u z hz
  else fun p => markedVerticalProjectiveLine (ZMod (p : ℕ))

theorem markedPhysicalEdgeRootLineEvent_forces {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p, p ∈ P j → p.Prime) {M : ℕ}
    (u : MarkedPhysicalMarking P (M+2)) (hS : Squarefree (markedPhysicalMarkingProduct u))
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod (markedPhysicalMarkingProduct u)))
    (z : ℤ × ℤ) (h : markedPhysicalEdgeRootLineEvent u hS g z) :
    markedRootKernelTuple hS g = markedPhysicalEdgeRootAssignedLines u z := by
  obtain ⟨hz,hinc⟩ := h
  rw [markedPhysicalEdgeRootAssignedLines, dite_eq_left hz]
  exact markedPhysicalEdgeLineIncidence_forces hP u hS g z hz hinc

def markedPhysicalActualEdgeRawSource {J : Type*} (e : J → ℝ) (x : ℝ)
    (u : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) (markedPadSlots x+1)) :
    MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x) :=
  (markedPhysicalMarkingEquiv (fun j => markedLogPowerBand (e j) x)
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) (markedPadSlots x)).symm
    (markedPhysicalEdgeSource u)

def markedPhysicalActualEdgeCopiedDivisor {J : Type*} [Fintype J] (e : J → ℝ) (x : ℝ)
    (u : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) (markedPadSlots x+1)) : ℤ :=
  (markedRawCopiedProduct
    ((markedRawActiveSplit ⌊(Real.log x)^(1/100 : ℝ)⌋₊) (markedPhysicalActualEdgeRawSource e x u)).1 : ℤ)

def markedPhysicalActualEdgeSourceProduct {J : Type*} [Fintype J] (e : J → ℝ) (x : ℝ)
    (u : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) (markedPadSlots x+1)) : ℤ :=
  (markedRawLastProduct
    ((markedRawActiveSplit ⌊(Real.log x)^(1/100 : ℝ)⌋₊) (markedPhysicalActualEdgeRawSource e x u)).2 : ℤ)

def markedPhysicalActualEdgeTargetProduct {J : Type*} [Fintype J] (e : J → ℝ) (x : ℝ)
    (u : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) (markedPadSlots x+1)) : ℤ :=
  ((∏ j, (u j (Fin.last (markedPadSlots x)) : ℕ)) : ℕ)

theorem markedPhysicalActualLineMain_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10 : ℝ) ≤ e j) (hinj : Function.Injective e) (T : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ d₀ Y : ℝ,
      Real.exp ((Real.log x)^(1/10 : ℝ)) ≤ Y →
      ∀ (u : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) (markedPadSlots x+1)),
        MarkedPhysicalMarkingDistinct u →
        ∀ [NeZero (markedPhysicalMarkingProduct u)]
          (hS : Squarefree (markedPhysicalMarkingProduct u))
          (A B C D : ℝ), A ≤ B → C ≤ D →
        ∀ (d b a : ℤ) (R Q W : ℝ) (ψ : ℝ → ℂ),
          1 ≤ Q → 1 ≤ Y → 0 ≤ R → 0 ≤ W →
          (∀ v, ‖ψ v‖ ≤ W) → (∀ v, ψ v ≠ 0 → |v| ≤ R) →
          markedPhysicalRootIncidenceMain Finset.univ (markedPhysicalMarkingProduct u) A B C D
            (markedPhysicalBadArcLower e x (markedPhysicalActualEdgeRawSource e x u) d₀ Y)
            (markedPhysicalBadArcUpper e x (markedPhysicalActualEdgeRawSource e x u) d₀ Y)
            (markedPhysicalBadArcCoefficient e x (markedPhysicalActualEdgeRawSource e x u) d₀ Y)
            d b a R Y Q ψ (markedPhysicalEdgeRootLineEvent u hS) ≤
          ((B-A)*(D-C)/(riemannZeta 2).re) * markedPhysicalProjectiveProduct u *
            ((33*W*(8*R+5))*Q^3) * (Real.log x)^(-T) := by
  filter_upwards [markedPhysicalBadRootIncidenceMain_log_saving e he hinj T,
    marked_array_disjoint_eventually e hinj] with x hx hdis
  intro d₀ Y hY u hu _hS0 hS A B C D hAB hCD d b a R Q W ψ hQ hYone hR hW hψ hsupp
  have hP : ∀ j p, p ∈ markedLogPowerBand (e j) x → p.Prime :=
    fun _ _ hp => (mem_markedLogPowerBand.mp hp).1
  have hh := hx d₀ Y hY (markedPhysicalActualEdgeRawSource e x u)
    (markedPhysicalMarkingProduct u) hS A B C D hAB hCD d b a R Q W ψ
    hQ hYone hR hW hψ hsupp (markedPhysicalEdgeRootLineEvent u hS)
    (markedPhysicalEdgeRootAssignedLines u)
    (fun z _ g hg => markedPhysicalEdgeRootLineEvent_forces hP u hS g z hg)
  rw [markedPhysicalRootLineMass_eq_projectiveProduct hP hdis u hu] at hh
  exact hh

def markedPhysicalActualUnionLineMain
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (x : ℝ)
    (hdis : Pairwise (fun i j => Disjoint (markedLogPowerBand (e i) x) (markedLogPowerBand (e j) x)))
    (d₀ Y A B C D : ℝ) (R Q : ℝ) (ψ : ℝ → ℂ) : ℝ :=
  ∑ u : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) (markedPadSlots x+1),
    if hu : MarkedPhysicalMarkingDistinct u then
      let hP := fun j p (hp : p ∈ markedLogPowerBand (e j) x) => (mem_markedLogPowerBand.mp hp).1
      letI : NeZero (markedPhysicalMarkingProduct u) := ⟨(markedPhysicalMarkingProduct_pos hP u).ne'⟩
      let hS := markedPhysicalMarkingProduct_squarefree hP hdis u hu
      markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x+1) *
        markedPhysicalRootIncidenceMain Finset.univ (markedPhysicalMarkingProduct u) A B C D
          (markedPhysicalBadArcLower e x (markedPhysicalActualEdgeRawSource e x u) d₀ Y)
          (markedPhysicalBadArcUpper e x (markedPhysicalActualEdgeRawSource e x u) d₀ Y)
          (markedPhysicalBadArcCoefficient e x (markedPhysicalActualEdgeRawSource e x u) d₀ Y)
          (markedPhysicalActualEdgeCopiedDivisor e x u)
          (markedPhysicalActualEdgeSourceProduct e x u)
          (markedPhysicalActualEdgeTargetProduct e x u)
          R Y Q ψ (markedPhysicalEdgeRootLineEvent u hS)
    else 0

theorem markedPhysicalActualUnionLineMain_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10 : ℝ) ≤ e j) (hinj : Function.Injective e) (T : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (hdis : Pairwise (fun i j => Disjoint (markedLogPowerBand (e i) x) (markedLogPowerBand (e j) x)))
        (d₀ Y : ℝ), Real.exp ((Real.log x)^(1/10 : ℝ)) ≤ Y →
      ∀ A B C D : ℝ, A ≤ B → C ≤ D →
      ∀ (R Q W : ℝ) (ψ : ℝ → ℂ),
        1 ≤ Q → 1 ≤ Y → 0 ≤ R → 0 ≤ W →
        (∀ v, ‖ψ v‖ ≤ W) → (∀ v, ψ v ≠ 0 → |v| ≤ R) →
        markedPhysicalActualUnionLineMain e x hdis d₀ Y A B C D R Q ψ ≤
          ((B-A)*(D-C)/(riemannZeta 2).re) *
            ((33*W*(8*R+5))*Q^3) * (Real.log x)^(-T) := by
  have hepos : ∀ j, 0 < e j := fun j => by linarith [he j]
  have hband := eventually_all.mpr (fun j => marked_log_power_band_mass_eventually (hepos j))
  filter_upwards [markedPhysicalActualLineMain_log_saving e he hinj T,
    markedPhysical_actual_one_edge_label_mass e hepos, hband,
    eventually_gt_atTop (1 : ℝ)] with x hx hmass hbandx hx1
  intro hdis d₀ Y hY A B C D hAB hCD R Q W ψ hQ hYone hR hW hψ hsupp
  let V := fun j => bandReciprocalMass (markedLogPowerBand (e j) x)
  let K := ((B-A)*(D-C)/(riemannZeta 2).re) * ((33*W*(8*R+5))*Q^3) * (Real.log x)^(-T)
  have hσ : 0 ≤ markedPhysicalMass V (markedPadSlots x+1) :=
    markedPhysicalMass_nonneg _ _
      (fun j => ((by positivity : 0 < Real.log 2/2).trans (hbandx j).1).le)
  have hK : 0 ≤ K := by
    dsimp only [K]
    have hlog := (Real.log_pos hx1).le
    have hz := markedPhysicalRoot_zeta_two_pos
    have hBA := sub_nonneg.mpr hAB
    have hDC := sub_nonneg.mpr hCD
    positivity
  unfold markedPhysicalActualUnionLineMain
  calc
    _ ≤ ∑ u : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) (markedPadSlots x+1),
        K * (if MarkedPhysicalMarkingDistinct u then
          markedPhysicalMass V (markedPadSlots x+1) * markedPhysicalProjectiveProduct u else 0) := by
      apply Finset.sum_le_sum
      intro u _
      by_cases hu : MarkedPhysicalMarkingDistinct u
      · simp only [dite_eq_left hu, ite_eq_left hu]
        let hP := fun j p (hp : p ∈ markedLogPowerBand (e j) x) => (mem_markedLogPowerBand.mp hp).1
        let : NeZero (markedPhysicalMarkingProduct u) := ⟨(markedPhysicalMarkingProduct_pos hP u).ne'⟩
        have hh := hx d₀ Y hY u hu (markedPhysicalMarkingProduct_squarefree hP hdis u hu)
          A B C D hAB hCD
          (markedPhysicalActualEdgeCopiedDivisor e x u)
          (markedPhysicalActualEdgeSourceProduct e x u)
          (markedPhysicalActualEdgeTargetProduct e x u)
          R Q W ψ hQ hYone hR hW hψ hsupp
        simpa only [V, K, mul_assoc, mul_comm, mul_left_comm] using
          mul_le_mul_of_nonneg_left hh hσ
      · simp only [dite_eq_right hu, ite_eq_right hu, mul_zero, le_refl]
    _ = K * ∑ u : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) (markedPadSlots x+1),
        if MarkedPhysicalMarkingDistinct u then
          markedPhysicalMass V (markedPadSlots x+1) * markedPhysicalProjectiveProduct u else 0 :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ K := mul_le_of_le_one_right hK (hmass (markedPadSlots x))

end ArtinMatthews
