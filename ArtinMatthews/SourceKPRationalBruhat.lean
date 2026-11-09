module

public import ArtinMatthews.SourceKPNormalizedBorel
public import ArtinMatthews.SourceKPAdeleWeylCoordinates


set_option backward.privateInPublic true
@[expose] public section

/-! The rational Eisenstein summation set is the actual right-coset
quotient of the upper Borel in the projective group. Its closed and open
cells are represented by `1` and `w n(x)` for `x : F`. -/

namespace ArtinMatthews
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section

variable (F : Type*) [Field F]

def sourceKPRationalBorel : Subgroup PGL(2, F) :=
  (sourceGL2NormalizedBorel F).map ProjGenLinGroup.mk

theorem sourceKPRationalBorel_mk_mem_iff (g : GL (Fin 2) F) :
    ProjGenLinGroup.mk g ∈ sourceKPRationalBorel F ↔ g 1 0 = 0 := by
  constructor
  · rintro ⟨b, hb, hb'⟩
    obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hb'
    rw [← hu, sourceKPMatrix_right_scalar_entry, (sourceGL2NormalizedBorel_bottom F b hb).1, zero_mul]
  · intro hg
    let d := Units.mk0 (g 1 1) (sourceGL2_bottom_right_ne_zero g hg)
    let b := g * GeneralLinearGroup.scalar (Fin 2) d⁻¹
    have hb : b ∈ sourceGL2NormalizedBorel F := by
      change b 1 0 = 0 ∧ b 1 1 = 1
      dsimp only [b]
      rw [sourceKPMatrix_right_scalar_entry, sourceKPMatrix_right_scalar_entry, hg, zero_mul]
      exact ⟨rfl, d.val_inv⟩
    exact ⟨b, hb, by simp [b]⟩

theorem sourceKPRationalBorel_upper (x : F) :
    sourcePGL2Upper x ∈ sourceKPRationalBorel F :=
  ⟨_, sourceGL2NormalizedBorel_upper F x, rfl⟩

theorem sourceKPRationalBorel_diagonal (u : Fˣ) :
    sourcePGL2Diagonal u ∈ sourceKPRationalBorel F :=
  ⟨_, sourceGL2NormalizedBorel_diagonal F u, rfl⟩

def sourceKPRationalBruhatMatrix : Option F → GL (Fin 2) F
  | none => 1
  | some x => sourceGL2Weyl * sourceGL2Upper x

abbrev SourceKPRationalBorelCoset := Quotient (QuotientGroup.rightRel (sourceKPRationalBorel F))

def sourceKPRationalBorelCosetMk (g : PGL(2, F)) : SourceKPRationalBorelCoset F :=
  Quotient.mk'' g

theorem sourceKPRationalBorelCosetMk_eq_iff (g h : PGL(2, F)) :
    sourceKPRationalBorelCosetMk F g = sourceKPRationalBorelCosetMk F h ↔
      h * g⁻¹ ∈ sourceKPRationalBorel F :=
  Quotient.eq''.trans QuotientGroup.rightRel_apply

private theorem sourceKPBruhatUpper_mul (x y : F) :
    sourceGL2Upper x * sourceGL2Upper y = sourceGL2Upper (x + y) := by
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [sourceGL2Upper, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem sourceKPBruhatUpper_zero : sourceGL2Upper (0 : F) = 1 := by
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [sourceGL2Upper]

private theorem sourceKPBruhatUpper_inv (x : F) :
    (sourceGL2Upper x)⁻¹ = sourceGL2Upper (-x) := by
  apply inv_eq_of_mul_eq_one_right
  rw [sourceKPBruhatUpper_mul, add_neg_cancel, sourceKPBruhatUpper_zero]

private theorem sourceKPBruhatWeyl_sq :
    (sourceGL2Weyl : GL (Fin 2) F) * sourceGL2Weyl = 1 := by
  rw [← sourceKPWeylMatrix_field, sourceKPWeylMatrix_square]

private theorem sourceKPBruhatWeyl_inv :
    (sourceGL2Weyl : GL (Fin 2) F)⁻¹ = sourceGL2Weyl :=
  inv_eq_of_mul_eq_one_right (sourceKPBruhatWeyl_sq F)

private theorem sourceKPRationalBruhat_injective :
    Function.Injective (fun t : Option F =>
      sourceKPRationalBorelCosetMk F (ProjGenLinGroup.mk (sourceKPRationalBruhatMatrix F t))) := by
  intro x y h
  cases x <;> cases y
  · rfl
  · have hm := (sourceKPRationalBorelCosetMk_eq_iff F _ _).mp h
    rw [sourceKPRationalBruhatMatrix, sourceKPRationalBruhatMatrix, map_one, inv_one, mul_one,
      sourceKPRationalBorel_mk_mem_iff] at hm
    simp [sourceGL2_right_upper_bottom_left, sourceGL2Weyl] at hm
  · have hm := (sourceKPRationalBorelCosetMk_eq_iff F _ _).mp h.symm
    rw [sourceKPRationalBruhatMatrix, sourceKPRationalBruhatMatrix, map_one, inv_one, mul_one,
      sourceKPRationalBorel_mk_mem_iff] at hm
    simp [sourceGL2_right_upper_bottom_left, sourceGL2Weyl] at hm
  · rename_i x y
    have hm := (sourceKPRationalBorelCosetMk_eq_iff F _ _).mp h
    rw [sourceKPRationalBruhatMatrix, sourceKPRationalBruhatMatrix, ← map_inv, ← map_mul,
      sourceKPRationalBorel_mk_mem_iff, _root_.mul_inv_rev, ← mul_assoc,
      sourceKPBruhatWeyl_inv, sourceKPBruhatUpper_inv,
      mul_assoc (sourceGL2Weyl : GL (Fin 2) F), sourceKPBruhatUpper_mul,
      sourceGL2_right_weyl_bottom_left, sourceGL2_right_upper_bottom_right] at hm
    simpa [sourceGL2Weyl, add_neg_eq_zero, eq_comm] using hm

private theorem sourceKPRationalBruhat_surjective :
    Function.Surjective (fun t : Option F =>
      sourceKPRationalBorelCosetMk F (ProjGenLinGroup.mk (sourceKPRationalBruhatMatrix F t))) := by
  intro q
  obtain ⟨p, rfl⟩ := Quotient.exists_rep q
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective p
  by_cases h : g 1 0 = 0
  · refine ⟨none, (sourceKPRationalBorelCosetMk_eq_iff F _ _).mpr ?_⟩
    simpa [sourceKPRationalBruhatMatrix] using (sourceKPRationalBorel_mk_mem_iff F g).mpr h
  · let x := g 1 1 / g 1 0
    refine ⟨some x, (sourceKPRationalBorelCosetMk_eq_iff F _ _).mpr ?_⟩
    rw [sourceKPRationalBruhatMatrix, ← map_inv, ← map_mul, sourceKPRationalBorel_mk_mem_iff,
      _root_.mul_inv_rev, ← mul_assoc, sourceKPBruhatWeyl_inv, sourceKPBruhatUpper_inv,
      sourceGL2_right_weyl_bottom_left, sourceGL2_right_upper_bottom_right]
    rw [mul_neg, ← mul_div_assoc, mul_div_cancel_left₀ _ h, neg_add_cancel]

/-- The actual rational Borel quotient, with one closed cell and one
open cell parametrized by the ground field. -/
def sourceKPRationalBorelCosetEquiv : Option F ≃ SourceKPRationalBorelCoset F :=
  Equiv.ofBijective _ ⟨sourceKPRationalBruhat_injective F, sourceKPRationalBruhat_surjective F⟩

theorem sourceKPRationalBorelCosetEquiv_apply (t : Option F) :
    sourceKPRationalBorelCosetEquiv F t =
      sourceKPRationalBorelCosetMk F (ProjGenLinGroup.mk (sourceKPRationalBruhatMatrix F t)) :=
  rfl

end
end ArtinMatthews
