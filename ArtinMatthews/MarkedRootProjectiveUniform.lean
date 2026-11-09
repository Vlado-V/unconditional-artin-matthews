module

public import ArtinMatthews.FixedURootSLOrder
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.Projectivization.Cardinality


set_option backward.privateInPublic true
@[expose] public section

/-! Actual uniform root matrices give uniform kernel projective lines.
This is the finite-group step of PD root replacement, not an assumed
root-residue distribution estimate. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators LinearAlgebra.Projectivization

noncomputable instance markedProjectiveLineFintype {F : Type*} [Field F] [Fintype F] :
    Fintype (ℙ F (Fin 2 → F)) := Fintype.ofFinite _

/-- Exact finite averaging under any transitive group action. -/
theorem marked_finite_pretransitive_average {G X : Type*} [Group G] [Fintype G]
    [Fintype X] [MulAction G X] [MulAction.IsPretransitive G X] (b : X) (f : X → ℂ) :
    (Fintype.card G : ℂ)⁻¹*(∑ g : G, f (g • b)) =
      (Fintype.card X : ℂ)⁻¹*(∑ x : X, f x) := by
  classical
  have : Nonempty X := ⟨b⟩
  have hinv (x : X) : (∑ g : G, f (g • x))=∑ g : G, f (g • b) := by
    obtain ⟨k,hk⟩ := MulAction.exists_smul_eq G b x
    rw [← hk]
    simp only [← mul_smul]
    exact Equiv.sum_comp (Equiv.mulRight k) (fun g : G => f (g • b))
  have hbalance : (Fintype.card X : ℂ)*(∑ g : G, f (g • b)) =
      (Fintype.card G : ℂ)*(∑ x : X, f x) := by
    calc
      _ = ∑ x : X, ∑ g : G, f (g • x) := by simp only [hinv,Finset.sum_const,nsmul_eq_mul,Finset.card_univ]
      _ = ∑ g : G, ∑ x : X, f (g • x) := Finset.sum_comm
      _ = ∑ _g : G, ∑ x : X, f x := by
        apply Finset.sum_congr rfl
        intro g _
        exact Equiv.sum_comp (MulAction.toPerm g) f
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ]
  have hG : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hX : (Fintype.card X : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  linear_combination hbalance

/-- The source's vertical kernel line before applying the inverse root matrix. -/
def markedVerticalProjectiveLine (F : Type*) [Field F] : ℙ F (Fin 2 → F) :=
  Projectivization.mk F ![0,1] (by intro h; have hh := congrFun h 1; simp at hh)

/-- The literal first-row kernel line of a determinant-one root matrix. -/
def markedMatrixKernelLine {F : Type*} [Field F]
    (g : Matrix.SpecialLinearGroup (Fin 2) F) : ℙ F (Fin 2 → F) :=
  g⁻¹ • markedVerticalProjectiveLine F

/-- The literal nonzero vector spanning the first-row kernel. -/
def markedMatrixKernelVector {F : Type*} [Field F]
    (g : Matrix.SpecialLinearGroup (Fin 2) F) : Fin 2 → F := ![-g 0 1,g 0 0]

theorem markedMatrixKernelVector_nonzero {F : Type*} [Field F]
    (g : Matrix.SpecialLinearGroup (Fin 2) F) : markedMatrixKernelVector g ≠ 0 := by
  intro he
  have h₀ := congrFun he 0
  have h₁ := congrFun he 1
  simp only [markedMatrixKernelVector,Matrix.cons_val_zero,Matrix.cons_val_one,
    Pi.zero_apply,neg_eq_zero] at h₀ h₁
  have hd := g.prop
  rw [Matrix.det_fin_two,h₀,h₁] at hd
  simp at hd

/-- The inverse-action definition is the actual first-row kernel, retaining
the source root matrix convention rather than an arbitrary projective orbit. -/
theorem markedMatrixKernelLine_eq_mk {F : Type*} [Field F]
    (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    markedMatrixKernelLine g=Projectivization.mk F (markedMatrixKernelVector g)
      (markedMatrixKernelVector_nonzero g) := by
  rw [markedMatrixKernelLine,markedVerticalProjectiveLine,Projectivization.smul_mk]
  congr 1
  change ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ ![0,1] = _
  rw [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  ext i
  fin_cases i <;> simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two,markedMatrixKernelVector]

theorem markedMatrixKernelVector_row {F : Type*} [Field F]
    (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    g 0 0 * markedMatrixKernelVector g 0+g 0 1 * markedMatrixKernelVector g 1=0 := by
  simp only [markedMatrixKernelVector,Matrix.cons_val_zero,Matrix.cons_val_one]
  ring

/-- Actual projective-line cardinality is p+1, retaining the prime residue field. -/
theorem markedProjectiveLine_card (p : ℕ) [Fact p.Prime] :
    Nat.card (ℙ (ZMod p) (Fin 2 → ZMod p))=p+1 := by
  rw [Projectivization.card_of_finrank_two (ZMod p) (Fin 2 → ZMod p) (by simp)]
  simp only [Nat.card_eq_fintype_card,ZMod.card]

/-- A genuinely uniform finite SL₂ matrix has the exactly uniform first-row
kernel line, with the source normalization1/(p+1). -/
theorem marked_prime_root_kernel_line_average (p : ℕ) [Fact p.Prime]
    (f : (ℙ (ZMod p) (Fin 2 → ZMod p)) → ℂ) :
    (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) : ℂ)⁻¹*
      (∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod p), f (markedMatrixKernelLine g)) =
      ((p+1 : ℕ) : ℂ)⁻¹*(∑ ℓ : ℙ (ZMod p) (Fin 2 → ZMod p), f ℓ) := by
  classical
  have hh := marked_finite_pretransitive_average (G := Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
    (markedVerticalProjectiveLine (ZMod p)) f
  have hinv : (∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod p), f (markedMatrixKernelLine g)) =
      ∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod p), f (g • markedVerticalProjectiveLine (ZMod p)) := by
    simpa only [markedMatrixKernelLine,Equiv.inv_apply] using
      Equiv.sum_comp (Equiv.inv (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)))
        (fun g => f (g • markedVerticalProjectiveLine (ZMod p)))
  rw [hinv]
  simpa only [Fintype.card_eq_nat_card,markedProjectiveLine_card] using hh

end ArtinMatthews
