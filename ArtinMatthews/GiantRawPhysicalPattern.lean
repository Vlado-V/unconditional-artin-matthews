module

public import ArtinMatthews.GiantTwoSidedRawKernel
public import ArtinMatthews.GiantTwoSidedPatternKernel


set_option backward.privateInPublic true
@[expose] public section

/-! The literal raw edge is the empty-auxiliary physical pattern with one free slot. -/

namespace ArtinMatthews
open Finset
open scoped BigOperators ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev giantTwoSidedRawEmptyPattern (J : Type*) (k : ℕ) : J → Finset (Fin k) :=
  fun _ => ∅

def giantTwoSidedRawEmptyAuxiliary {J : Type*} (P : J → Finset ℕ) (k : ℕ) :
    GiantTwoSidedPatternAuxiliary P (giantTwoSidedRawEmptyPattern J k) :=
  fun _ i => (Finset.notMem_empty _ i.property).elim

def giantTwoSidedRawPrefixProduct {J : Type*} [Fintype J] {P : J → Finset ℕ} {k : ℕ}
    (a : MarkedPhysicalMarking P (k+1)) : ℕ :=
  markedPhysicalMarkingProduct (markedPhysicalMarkingSplit k a).1

theorem giantTwoSidedRaw_copiedProduct {J : Type*} [Fintype J] {P : J → Finset ℕ} {k : ℕ}
    (a : MarkedPhysicalMarking P (k+1)) :
    giantTwoSidedPatternCopiedProduct (giantTwoSidedRawEmptyPattern J k) a =
      giantTwoSidedRawPrefixProduct a := by
  simp only [giantTwoSidedPatternCopiedProduct, giantTwoSidedRawEmptyPattern, sdiff_empty,
    giantTwoSidedRawPrefixProduct, markedPhysicalMarkingProduct, markedPhysicalMarkingSplit,
    Equiv.coe_fn_mk]
  rfl

private theorem rawAuxiliaryProduct_one {J : Type*} [Fintype J] {P : J → Finset ℕ} {k : ℕ}
    (aux : GiantTwoSidedPatternAuxiliary P (giantTwoSidedRawEmptyPattern J k)) :
    giantTwoSidedPatternAuxiliaryProduct aux = 1 := by
  simp [giantTwoSidedPatternAuxiliaryProduct]

private theorem rawAuxiliaryMass_one {J : Type*} [Fintype J] {P : J → Finset ℕ} {k : ℕ}
    (aux : GiantTwoSidedPatternAuxiliary P (giantTwoSidedRawEmptyPattern J k)) :
    giantTwoSidedPatternAuxiliaryMass aux = 1 := by
  simp [giantTwoSidedPatternAuxiliaryMass]

private theorem rawFreshMass_eq {J : Type*} [Fintype J] (P : J → Finset ℕ) (k : ℕ) :
    giantTwoSidedPatternFreshMass P (giantTwoSidedRawEmptyPattern J k) 1 =
      ∏ j, (bandReciprocalMass (P j))⁻¹ := by
  simp [giantTwoSidedPatternFreshMass]

theorem giantTwoSidedRaw_patternCondition_iff {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k : ℕ} {Z Z' : Finset ℕ}
    (s : GiantTwoSidedEndpointState P (k+1) Z) (t : GiantTwoSidedEndpointState P (k+1) Z')
    (aux : GiantTwoSidedPatternAuxiliary P (giantTwoSidedRawEmptyPattern J k)) :
    GiantTwoSidedPatternCondition (giantTwoSidedRawEmptyPattern J k) 1 s t aux ↔
      GiantTwoSidedRawPhysicalCondition s t := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · funext j i
      exact (h.1 j i (Finset.notMem_empty i)).symm
    · have hs := h.2.1
      rw [giantTwoSidedRaw_copiedProduct, rawAuxiliaryProduct_one, mul_one, one_mul] at hs
      change t.val.1.val = s.val.1.val + giantTwoSidedRawPrefixProduct s.val.2
      exact_mod_cast hs
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro j i _
      exact (congrFun (congrFun h.1 j) i).symm
    · rw [giantTwoSidedRaw_copiedProduct, rawAuxiliaryProduct_one, mul_one, one_mul]
      have hs : t.val.1.val = s.val.1.val + giantTwoSidedRawPrefixProduct s.val.2 := h.2
      exact_mod_cast hs
    · intro g j i l
      exact (Finset.notMem_empty _ i.property).elim

/-- The unchanged fixed-character factor at the copied product. -/
def giantTwoSidedRawPatternCoefficient {J : Type*} [Fintype J] {P : J → Finset ℕ}
    {k m : ℕ} (χ : DirichletCharacter ℂ m) :
    GiantTwoSidedPatternCoefficient P (giantTwoSidedRawEmptyPattern J k) 1 :=
  fun a _ _ => conj (χ (giantTwoSidedRawPrefixProduct a))

/-- The root weight is evaluated on the same copied slots as the physical coefficient. -/
def giantTwoSidedRawPatternEntry {J : Type*} [Fintype J] {P : J → Finset ℕ}
    {k m : ℕ} {Z Z' : Finset ℕ} (q ζ : ℝ) (χ : DirichletCharacter ℂ m) (R : ℕ → ℕ → ℂ)
    (s : GiantTwoSidedEndpointState P (k+1) Z) (t : GiantTwoSidedEndpointState P (k+1) Z') : ℂ :=
  R s.val.1.val (giantTwoSidedRawPrefixProduct s.val.2) *
    giantTwoSidedPatternPhysicalCoefficient 1 q ζ (giantTwoSidedRawPatternCoefficient χ)
      s t (giantTwoSidedRawEmptyAuxiliary P k)

theorem giantTwoSidedRawPatternEntry_zero {J : Type*} [Fintype J] {P : J → Finset ℕ}
    {k m : ℕ} {Z Z' : Finset ℕ} (q ζ : ℝ) (χ : DirichletCharacter ℂ m) (R : ℕ → ℕ → ℂ)
    (s : GiantTwoSidedEndpointState P (k+1) Z) (t : GiantTwoSidedEndpointState P (k+1) Z')
    (h : ¬ GiantTwoSidedRawPhysicalCondition s t) :
    giantTwoSidedRawPatternEntry q ζ χ R s t = 0 := by
  unfold giantTwoSidedRawPatternEntry giantTwoSidedPatternPhysicalCoefficient
  rw [ite_eq_right (fun he => h ((giantTwoSidedRaw_patternCondition_iff s t _).mp he)), mul_zero]

def giantTwoSidedRawPairLeft {J : Type*} [Fintype J] (P : J → Finset ℕ) (k : ℕ)
    (q : ℝ) (F L : ℕ → ℂ) (n : ℕ) : ℂ :=
  conj (F n) * (giantTwoSidedEndpointDamping P (k+1) q n : ℂ) * conj (L n)

def giantTwoSidedRawPairRight {J : Type*} [Fintype J] (P : J → Finset ℕ) (k : ℕ)
    {m : ℕ} (q : ℝ) (χ : DirichletCharacter ℂ m) (G : ℕ → ℂ) (n : ℕ) : ℂ :=
  χ n * G n * (giantTwoSidedEndpointDamping P (k+1) q n : ℂ)

theorem giantTwoSidedRawPhysicalTerm_eq_pattern_pairing {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k m : ℕ} {Z Z' : Finset ℕ}
    (x q : ℝ) (Ψ : ℝ → ℂ) (χ : DirichletCharacter ℂ m) (F G L : ℕ → ℂ)
    (e : GiantTwoSidedRawPhysicalEdge P k Z Z') :
    L e.val.1.val.1.val * giantTwoSidedRawPhysicalTerm x q Ψ χ F G e =
      (markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+1) : ℂ) *
      giantTwoSidedRawPatternEntry q 0 χ
        (fun n D => Ψ ((n : ℝ)/(x*(D : ℝ)))/(n : ℂ)) e.val.1 e.val.2 *
      star (giantTwoSidedRawPairLeft P k q F L e.val.1.val.1.val) *
      giantTwoSidedRawPairRight P k q χ G e.val.2.val.1.val := by
  have hshift : e.val.2.val.1.val = e.val.1.val.1.val +
      giantTwoSidedRawPrefixProduct e.val.1.val.2 := e.property.2
  have hdiff : e.val.2.val.1.val - e.val.1.val.1.val =
      giantTwoSidedRawPrefixProduct e.val.1.val.2 := by
    rw [hshift, Nat.add_sub_cancel_left]
  have hgate := (giantTwoSidedRaw_patternCondition_iff e.val.1 e.val.2
    (giantTwoSidedRawEmptyAuxiliary P k)).mpr e.property
  simp only [giantTwoSidedRawPhysicalTerm, giantTwoSidedRawPatternEntry,
    giantTwoSidedPatternPhysicalCoefficient, ite_eq_left hgate, rawAuxiliaryMass_one,
    rawAuxiliaryProduct_one, rawFreshMass_eq, giantTwoSidedRawPatternCoefficient,
    giantTwoSidedRawPairLeft, giantTwoSidedRawPairRight, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_one, Complex.ofReal_zero, zero_mul, Complex.cpow_zero, star_mul,
    Complex.star_def, Complex.conj_conj, Complex.conj_ofReal, hdiff, giantTwoSidedRawPrefixProduct]
  ring

end
end ArtinMatthews
