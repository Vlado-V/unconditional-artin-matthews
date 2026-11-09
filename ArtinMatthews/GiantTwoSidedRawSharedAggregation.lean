module

public import ArtinMatthews.GiantTwoSidedRawKernel
public import ArtinMatthews.GiantTwoSidedSharedRestoration
public import ArtinMatthews.GiantTwoSidedFreeMarking


set_option backward.privateInPublic true
@[expose] public section

/-! Reindex the exact raw shared-edge sum by its quotient position,
actual free labels and admissible shared lists. Both physical position
tests are retained in the equivalence through the literal coverage law. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev GiantTwoSidedRawHarmonicEdge {J : Type*} (P : J → Finset ℕ) (k N : ℕ) :=
  Σ w : ↥(Ioc 0 N), Σ b : GiantTwoSidedFreeMarking P w.val,
    Σ b' : GiantTwoSidedFreeMarking P (w.val+1),
      {c : MarkedPhysicalMarking P k // GiantTwoSidedSharedAdmissible c b.val b'.val}

def giantTwoSidedRawSharedHarmonicEquiv {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k N : ℕ} {Z Z' : Finset ℕ}
    (hcover : ∀ (c : MarkedPhysicalMarking P k) (w : ↥(Ioc 0 N)),
      markedPhysicalMarkingProduct c*w.val ∈ Z ∧
        markedPhysicalMarkingProduct c*(w.val+1) ∈ Z') :
    GiantTwoSidedRawSharedEdge P k N Z Z' ≃ GiantTwoSidedRawHarmonicEdge P k N where
  toFun a := ⟨a.val.2.1,⟨a.val.2.2.1,a.property.2.2.2.1⟩,
    ⟨a.val.2.2.2,a.property.2.2.2.2.1⟩,⟨a.val.1,a.property.1,a.property.2.1,a.property.2.2.1⟩⟩
  invFun a := ⟨(a.2.2.2.val,a.1,a.2.1.val,a.2.2.1.val),
    a.2.2.2.property.1,a.2.2.2.property.2.1,a.2.2.2.property.2.2,
      a.2.1.property,a.2.2.1.property,hcover a.2.2.2.val a.1⟩
  left_inv a := by cases a; rfl
  right_inv a := by cases a; rfl

def giantTwoSidedRawPositionKernel {m : ℕ} (x : ℝ) (Ψ : ℝ → ℂ)
    (χ : DirichletCharacter ℂ m) (F G : ℕ → ℂ) (w : ℕ) : ℂ :=
  (Ψ ((w:ℝ)/x)/(w:ℂ))*F w*χ (w+1:ℕ)*G (w+1)

def giantTwoSidedNormalizedMarkWeight {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (k : ℕ) (q : ℝ) (w : ℕ) : ℝ :=
  (∏ j,(bandReciprocalMass (P j))⁻¹)^2 *
    ∑ b : GiantTwoSidedFreeMarking P w, ∑ b' : GiantTwoSidedFreeMarking P (w+1),
      giantTwoSidedSharedNormalizedDamping k q w b.val b'.val

theorem giantTwoSidedSharedNormalizedDamping_eq_admissible_sum {J : Type*}
    [Fintype J] [DecidableEq J] {P : J → Finset ℕ} (k : ℕ) (q : ℝ) (w : ℕ)
    (b b' : (j : J) → ↥(P j)) :
    giantTwoSidedSharedNormalizedDamping k q w b b' =
      ∑ c : {c : MarkedPhysicalMarking P k // GiantTwoSidedSharedAdmissible c b b'},
        markedPhysicalPadHarmonicMass P k c.val *
          ((giantTwoSidedEndpointDamping P (k+1) q (markedPhysicalMarkingProduct c.val*w))^2 *
            (giantTwoSidedEndpointDamping P (k+1) q (markedPhysicalMarkingProduct c.val*(w+1)))^2) := by
  classical
  let valid (c : MarkedPhysicalMarking P k) : Prop := GiantTwoSidedSharedAdmissible c b b'
  let full (c : MarkedPhysicalMarking P k) :=
    (giantTwoSidedEndpointDamping P (k+1) q (markedPhysicalMarkingProduct c*w))^2 *
      (giantTwoSidedEndpointDamping P (k+1) q (markedPhysicalMarkingProduct c*(w+1)))^2
  let term (c : MarkedPhysicalMarking P k) := markedPhysicalPadHarmonicMass P k c*full c
  have hs := Finset.sum_subtype (p := valid) (F := inferInstance)
    (univ.filter valid) (by simp) term
  change giantTwoSidedSharedNormalizedDamping k q w b b' = ∑ c : Subtype valid,term c.val
  rw [← hs, sum_filter, giantTwoSidedSharedNormalizedDamping]
  apply sum_congr rfl
  intro c _
  by_cases hc : GiantTwoSidedSharedAdmissible c b b' <;>
    simp [giantTwoSidedSharedGuardedDamping,term,full,hc]

theorem giantTwoSidedRawShared_sum_eq_harmonic {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k m N : ℕ} {Z Z' : Finset ℕ}
    (hcover : ∀ (c : MarkedPhysicalMarking P k) (w : ↥(Ioc 0 N)),
      markedPhysicalMarkingProduct c*w.val ∈ Z ∧
        markedPhysicalMarkingProduct c*(w.val+1) ∈ Z')
    (x q : ℝ) (Ψ : ℝ → ℂ) (χ : DirichletCharacter ℂ m) (F G : ℕ → ℂ) :
    (∑ a : GiantTwoSidedRawSharedEdge P k N Z Z',giantTwoSidedRawSharedTerm x q Ψ χ F G a) =
      ∑ w ∈ Ioc 0 N,giantTwoSidedRawPositionKernel x Ψ χ F G w *
        (giantTwoSidedNormalizedMarkWeight P k q w:ℂ) := by
  classical
  rw [← (giantTwoSidedRawSharedHarmonicEquiv hcover).symm.sum_comp
      (giantTwoSidedRawSharedTerm x q Ψ χ F G)]
  simp only [Fintype.sum_sigma]
  rw [← Finset.sum_coe_sort (Ioc 0 N) (fun w => giantTwoSidedRawPositionKernel x Ψ χ F G w *
    (giantTwoSidedNormalizedMarkWeight P k q w:ℂ))]
  apply sum_congr rfl
  intro w _
  let K := giantTwoSidedRawPositionKernel x Ψ χ F G w.val
  let B := ∏ j,(bandReciprocalMass (P j))⁻¹
  rw [giantTwoSidedNormalizedMarkWeight,Complex.ofReal_mul,← mul_assoc]
  change _ = (K*((B^2:ℝ):ℂ))*((∑ b : GiantTwoSidedFreeMarking P w.val,
    ∑ b' : GiantTwoSidedFreeMarking P (w.val+1),
      giantTwoSidedSharedNormalizedDamping k q w.val b.val b'.val : ℝ):ℂ)
  simp only [Complex.ofReal_sum,Finset.mul_sum]
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro b' _
  rw [giantTwoSidedSharedNormalizedDamping_eq_admissible_sum]
  simp only [Complex.ofReal_sum,Finset.mul_sum]
  apply sum_congr rfl
  intro c _
  simp only [giantTwoSidedRawSharedTerm, giantTwoSidedRawSharedHarmonicEquiv,
    Equiv.coe_fn_symm_mk, Complex.ofReal_mul, K, giantTwoSidedRawPositionKernel, B]
  ring

end
end ArtinMatthews
