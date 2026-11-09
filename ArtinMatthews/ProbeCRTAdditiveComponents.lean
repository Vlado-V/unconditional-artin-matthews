module

public import ArtinMatthews.ProbePrimitiveCharacterShift
public import Mathlib.Algebra.BigOperators.Pi


set_option backward.privateInPublic true
@[expose] public section

/-! Exact decomposition of a genuine additive character through a finite
ring product, retaining its induced component characters. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open scoped BigOperators Classical
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (A : ι → Type*) [∀ i, CommRing (A i)]

def probePiSingle (i : ι) : A i →+ (∀ j, A j) where
  toFun := Pi.single i
  map_zero' := by ext j; simp
  map_add' x y := by
    ext j
    by_cases h : i = j
    · subst j; simp
    · simp only [Pi.single_eq_of_ne' h, Pi.add_apply, add_zero]

omit [Fintype ι] in
theorem probeAddChar_sum {R : Type*} [AddCommMonoid R] (ψ : AddChar R ℂ)
    (s : Finset ι) (f : ι → R) : ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.sum_insert ha, Finset.prod_insert ha,
      AddChar.map_add_eq_mul, ih]

def probePiAddCharComponent (ψ : AddChar (∀ i, A i) ℂ) (i : ι) : AddChar (A i) ℂ :=
  ψ.compAddMonoidHom (probePiSingle A i)

theorem probePiAddChar_factor (ψ : AddChar (∀ i, A i) ℂ) (x : ∀ i, A i) :
    ψ x = ∏ i, probePiAddCharComponent A ψ i (x i) := by
  have hx : (∑ i, Pi.single i (x i)) = x := Finset.univ_sum_single x
  calc
    ψ x = ψ (∑ i, Pi.single i (x i)) := congrArg ψ hx.symm
    _ = ∏ i, ψ (Pi.single i (x i)) := probeAddChar_sum ψ _ _
    _ = _ := rfl

omit [Fintype ι] in
theorem probePiAddCharComponent_primitive (ψ : AddChar (∀ i, A i) ℂ)
    (hψ : ψ.IsPrimitive) (i : ι) : (probePiAddCharComponent A ψ i).IsPrimitive := by
  intro a ha he
  have hsingle : Pi.single i a ≠ (0 : ∀ j, A j) := by
    intro hh
    have hi := congrFun hh i
    apply ha
    simpa using hi
  apply hψ hsingle
  ext x
  have ht := congrArg (fun φ : AddChar (A i) ℂ => φ (x i)) he
  have hmul : Pi.single i a * x = Pi.single i (a * x i) := by
    ext j
    by_cases h : i = j
    · subst j; simp
    · simp only [Pi.single_eq_of_ne' h, Pi.mul_apply, zero_mul]
  change ψ (Pi.single i (a * x i)) = 1 at ht
  change ψ (Pi.single i a * x) = 1
  rw [hmul]
  exact ht

variable {B : Type*} [CommRing B]

theorem probeAddChar_transport_primitive {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (ψ : AddChar S ℂ) (hψ : ψ.IsPrimitive) :
    (ψ.compAddMonoidHom e.toAddMonoidHom).IsPrimitive := by
  intro x hx he
  have hex : e x ≠ 0 := by
    intro hh
    apply hx
    apply e.injective
    simpa only [map_zero] using hh
  apply hψ hex
  ext y
  obtain ⟨y, rfl⟩ := e.surjective y
  have ht := congrArg (fun φ : AddChar R ℂ => φ y) he
  change ψ (e (x * y)) = 1 at ht
  simpa only [map_mul, AddChar.mulShift_apply, AddChar.one_apply] using ht

def probeCRTAddCharComponent (e : B ≃+* ∀ i, A i) (ψ : AddChar B ℂ) (i : ι) :
    AddChar (A i) ℂ :=
  probePiAddCharComponent A (ψ.compAddMonoidHom e.symm.toAddMonoidHom) i

theorem probeCRTAddChar_factor (e : B ≃+* ∀ i, A i) (ψ : AddChar B ℂ) (x : B) :
    ψ x = ∏ i, probeCRTAddCharComponent A e ψ i (e x i) := by
  have he := probePiAddChar_factor A (ψ.compAddMonoidHom e.symm.toAddMonoidHom) (e x)
  change ψ (e.symm (e x)) = ∏ i, probeCRTAddCharComponent A e ψ i (e x i) at he
  simpa only [RingEquiv.symm_apply_apply] using he

omit [Fintype ι] in
theorem probeCRTAddCharComponent_primitive (e : B ≃+* ∀ i, A i)
    (ψ : AddChar B ℂ) (hψ : ψ.IsPrimitive) (i : ι) :
    (probeCRTAddCharComponent A e ψ i).IsPrimitive :=
  probePiAddCharComponent_primitive A _ (probeAddChar_transport_primitive e.symm ψ hψ) i

end
end ArtinMatthews.VaryingKummerAnalytic
