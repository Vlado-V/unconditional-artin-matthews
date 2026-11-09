module

public import ArtinMatthews.IdealProductAverage
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.Analysis.InnerProductSpace.PiL2


set_option backward.privateInPublic true
@[expose] public section

/-! A product orthonormal basis gives a concrete finite Hoeffding
transform. The distinguished coordinate vector is the probability root. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
attribute [local instance] Classical.propDecidable

def idealProbabilityRoot {α : Type*} [Fintype α] (w : α → ℝ) : EuclideanSpace ℂ α :=
  WithLp.toLp 2 (fun a => (Real.sqrt (w a):ℂ))

theorem idealProbabilityRoot_norm {α : Type*} [Fintype α]
    (w : α → ℝ) (hw : ∀ a,0 ≤ w a) (hs : ∑ a,w a=1) :
    ‖idealProbabilityRoot w‖=1 := by
  have hsq : ‖idealProbabilityRoot w‖^2=1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [idealProbabilityRoot,WithLp.ofLp_toLp,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hw _)]
    exact hs
  nlinarith [norm_nonneg (idealProbabilityRoot w)]

theorem idealCoordinateBasis_exists {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ℝ) (hw : ∀ a,0 ≤ w a) (hs : ∑ a,w a=1) (a₀ : α) :
    ∃ b : OrthonormalBasis α ℂ (EuclideanSpace ℂ α),b a₀=idealProbabilityRoot w := by
  have hon : Orthonormal ℂ (({a₀} : Set α).domRestrict (fun _ => idealProbabilityRoot w)) := by
    rw [orthonormal_subsingleton_iff]
    intro a
    exact idealProbabilityRoot_norm w hw hs
  obtain ⟨b,hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq
    (show Module.finrank ℂ (EuclideanSpace ℂ α)=Fintype.card α by simp)
  exact ⟨b,hb a₀ (Set.mem_singleton a₀)⟩

theorem idealTuple_sum_product {J A : Type*} [Fintype J] [DecidableEq J]
    [CommSemiring A] {P : J → Finset ℕ} {M : ℕ}
    (f : ∀ j,Fin M → ↥(P j) → A) :
    (∑ a : MarkedPhysicalMarking P M,∏ j,∏ i,f j i (a j i))=
      ∏ j,∏ i,∑ p : ↥(P j),f j i p := by
  rw [← Fintype.prod_sum (fun j (a : Fin M → ↥(P j)) => ∏ i,f j i (a i))]
  apply prod_congr rfl
  intro j _
  exact (Fintype.prod_sum (f j)).symm

def idealProductBasisVector {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M : ℕ}
    (b : ∀ j,OrthonormalBasis ↥(P j) ℂ (EuclideanSpace ℂ ↥(P j)))
    (t : MarkedPhysicalMarking P M) : EuclideanSpace ℂ (MarkedPhysicalMarking P M) :=
  WithLp.toLp 2 (fun a => ∏ j,∏ i,(b j (t j i)) (a j i))

theorem idealProductBasisVector_inner {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {M : ℕ}
    (b : ∀ j,OrthonormalBasis ↥(P j) ℂ (EuclideanSpace ℂ ↥(P j)))
    (s t : MarkedPhysicalMarking P M) :
    ⟪idealProductBasisVector b s,idealProductBasisVector b t⟫_ℂ=
      ∏ j,∏ i,⟪b j (s j i),b j (t j i)⟫_ℂ := by
  simp only [idealProductBasisVector,EuclideanSpace.inner_toLp_toLp,dotProduct,
    Pi.star_apply,star_prod,← prod_mul_distrib]
  rw [idealTuple_sum_product (fun j i p =>
    (b j (t j i)) p * star ((b j (s j i)) p))]
  rfl

theorem idealProductBasisVector_orthonormal {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {M : ℕ}
    (b : ∀ j,OrthonormalBasis ↥(P j) ℂ (EuclideanSpace ℂ ↥(P j))) :
    Orthonormal ℂ (idealProductBasisVector (M:=M) b) := by
  rw [orthonormal_iff_ite]
  intro s t
  rw [idealProductBasisVector_inner]
  by_cases hst : s=t
  · subst t
    have hi (j : J) (i : Fin M) : ⟪b j (s j i),b j (s j i)⟫_ℂ=1 :=
      ((orthonormal_iff_ite.mp (b j).orthonormal) _ _).trans (ite_eq_left rfl)
    simp_rw [hi]
    simp
  · rw [ite_eq_right hst]
    have hne : ∃ j i,s j i≠t j i := by
      by_contra h
      push Not at h
      exact hst (funext fun j => funext fun i => h j i)
    obtain ⟨j,i,hi⟩ := hne
    apply prod_eq_zero (mem_univ j)
    apply prod_eq_zero (mem_univ i)
    exact ((orthonormal_iff_ite.mp (b j).orthonormal) _ _).trans (ite_eq_right hi)

def idealProductBasis {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {M : ℕ}
    (b : ∀ j,OrthonormalBasis ↥(P j) ℂ (EuclideanSpace ℂ ↥(P j))) :
    OrthonormalBasis (MarkedPhysicalMarking P M) ℂ (EuclideanSpace ℂ (MarkedPhysicalMarking P M)) :=
  (basisOfLinearIndependentOfCardEqFinrank' (idealProductBasisVector b)
    (idealProductBasisVector_orthonormal b).linearIndependent (by simp)).toOrthonormalBasis
      (by simpa only [coe_basisOfLinearIndependentOfCardEqFinrank'] using idealProductBasisVector_orthonormal b)

theorem idealProductBasis_apply {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {M : ℕ}
    (b : ∀ j,OrthonormalBasis ↥(P j) ℂ (EuclideanSpace ℂ ↥(P j)))
    (t : MarkedPhysicalMarking P M) :
    idealProductBasis b t=idealProductBasisVector b t := by
  simp [idealProductBasis,Module.Basis.coe_toOrthonormalBasis]

def idealWeightedVector {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (f : MarkedPhysicalMarking P M → ℂ) :
    EuclideanSpace ℂ (MarkedPhysicalMarking P M) :=
  WithLp.toLp 2 (fun a => (Real.sqrt (idealLabelMass P M a):ℂ)*f a)

theorem idealWeightedVector_norm_sq {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (f : MarkedPhysicalMarking P M → ℂ) :
    ‖idealWeightedVector P f‖^2=idealLabelEnergy P M f := by
  rw [EuclideanSpace.norm_sq_eq]
  apply sum_congr rfl
  intro a _
  simp only [idealWeightedVector,WithLp.ofLp_toLp,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (idealLabelMass_nonneg P M hV a)]

def idealHoeffdingTransform {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ}
    (b : ∀ j,OrthonormalBasis ↥(P j) ℂ (EuclideanSpace ℂ ↥(P j)))
    (f : MarkedPhysicalMarking P M → ℂ) : MarkedPhysicalMarking P M → ℂ :=
  fun t => (idealProductBasis b).repr (idealWeightedVector P f) t

theorem idealHoeffdingTransform_energy {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (b : ∀ j,OrthonormalBasis ↥(P j) ℂ (EuclideanSpace ℂ ↥(P j)))
    (f : MarkedPhysicalMarking P M → ℂ) :
    (∑ t : MarkedPhysicalMarking P M,‖idealHoeffdingTransform P b f t‖^2)=idealLabelEnergy P M f := by
  rw [← idealWeightedVector_norm_sq P hV f,← (idealProductBasis b).repr.norm_map]
  exact (EuclideanSpace.norm_sq_eq _).symm

end
end ArtinMatthews
