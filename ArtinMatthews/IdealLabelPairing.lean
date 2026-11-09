module

public import ArtinMatthews.IdealProductBasis


set_option backward.privateInPublic true
@[expose] public section

/-! The actual harmonic pairing and its Cauchy bound retain arbitrary
full-tuple tests, including complex phases of modulus one. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
attribute [local instance] Classical.propDecidable

def idealLabelPairing {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (f g : MarkedPhysicalMarking P M → ℂ) : ℂ :=
  ∑ a,(idealLabelMass P M a:ℂ)*star (f a)*g a

def idealLabelNorm {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (f : MarkedPhysicalMarking P M → ℂ) : ℝ :=
  Real.sqrt (idealLabelEnergy P M f)

theorem idealLabelPairing_inner {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (f g : MarkedPhysicalMarking P M → ℂ) :
    idealLabelPairing P f g=⟪idealWeightedVector P f,idealWeightedVector P g⟫_ℂ := by
  change (∑ a,(idealLabelMass P M a:ℂ)*star (f a)*g a)=
    ∑ a,((Real.sqrt (idealLabelMass P M a):ℂ)*g a)*star ((Real.sqrt (idealLabelMass P M a):ℂ)*f a)
  apply sum_congr rfl
  intro a _
  have hs : (Real.sqrt (idealLabelMass P M a):ℂ)^2=(idealLabelMass P M a:ℂ) := by
    rw [← Complex.ofReal_pow,Real.sq_sqrt (idealLabelMass_nonneg P M hV a)]
  simp only [star_mul,Complex.star_def,Complex.conj_ofReal]
  rw [← hs]
  ring

theorem idealLabelNorm_eq_weighted {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (f : MarkedPhysicalMarking P M → ℂ) :
    idealLabelNorm P f=‖idealWeightedVector P f‖ := by
  rw [idealLabelNorm,← idealWeightedVector_norm_sq P hV f,Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _)]

theorem idealLabelPairing_norm_le {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (f g : MarkedPhysicalMarking P M → ℂ) :
    ‖idealLabelPairing P f g‖ ≤ idealLabelNorm P f*idealLabelNorm P g := by
  rw [idealLabelPairing_inner P hV,idealLabelNorm_eq_weighted P hV,idealLabelNorm_eq_weighted P hV]
  exact norm_inner_le_norm _ _

theorem idealLabelEnergy_phase {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (f phase : MarkedPhysicalMarking P M → ℂ)
    (hphase : ∀ a,‖phase a‖=1) :
    idealLabelEnergy P M (fun a => f a*phase a)=idealLabelEnergy P M f := by
  unfold idealLabelEnergy
  simp only [norm_mul,hphase,mul_one]

theorem idealLabelPairing_phase_norm_le {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (f g phase : MarkedPhysicalMarking P M → ℂ) (hphase : ∀ a,‖phase a‖=1) :
    ‖idealLabelPairing P f (fun a => g a*phase a)‖ ≤ idealLabelNorm P f*idealLabelNorm P g := by
  have h := idealLabelPairing_norm_le P hV f (fun a => g a*phase a)
  simpa only [idealLabelNorm,idealLabelEnergy_phase P g phase hphase] using h

end
end ArtinMatthews
