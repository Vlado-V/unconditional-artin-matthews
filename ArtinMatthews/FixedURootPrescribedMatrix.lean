module

public import ArtinMatthews.FixedURootBoxMain


set_option backward.privateInPublic true
@[expose] public section

/-! Integer representatives of every prescribed special-linear matrix and
the literal entrywise meaning of its root-completion congruence. -/
namespace ArtinMatthews

/-- Canonical integer representatives of entries of the prescribed matrix. -/
noncomputable def fixedURootMatrixEntry {S : ℕ}
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) (i j : Fin 2) : ℤ :=
  ((g₀ i j).val : ℤ)

@[simp] theorem fixedURootMatrixEntry_cast {S : ℕ} [NeZero S]
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) (i j : Fin 2) :
    (fixedURootMatrixEntry g₀ i j : ZMod S) = g₀ i j := by
  simp only [fixedURootMatrixEntry,Int.cast_natCast,ZMod.natCast_zmod_val]

/-- Every prescribed matrix supplies the exact determinant-one integer
congruence required by the root-count theorem. -/
theorem fixedURootMatrixEntry_det {S : ℕ} [NeZero S]
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) :
    Int.ModEq (S : ℤ)
      (fixedURootMatrixEntry g₀ 0 0 * fixedURootMatrixEntry g₀ 1 1 -
        fixedURootMatrixEntry g₀ 0 1 * fixedURootMatrixEntry g₀ 1 0) 1 := by
  apply (ZMod.intCast_eq_intCast_iff _ _ S).mp
  simpa only [Int.cast_sub,Int.cast_mul,Int.cast_one,fixedURootMatrixEntry_cast,
    Matrix.det_fin_two] using g₀.prop

/-- Entrywise reduction of an actual integer root matrix equals the
prescribed matrix exactly when the four displayed congruences hold. -/
theorem fixedURootMatrix_modEq_iff {S : ℕ} [NeZero S]
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) (u c v d : ℤ) :
    ((!![(u : ZMod S), (c : ZMod S); (v : ZMod S), (d : ZMod S)] :
        Matrix (Fin 2) (Fin 2) (ZMod S)) = (g₀ : Matrix (Fin 2) (Fin 2) (ZMod S))) ↔
      Int.ModEq (S : ℤ) u (fixedURootMatrixEntry g₀ 0 0) ∧
      Int.ModEq (S : ℤ) c (fixedURootMatrixEntry g₀ 0 1) ∧
      Int.ModEq (S : ℤ) v (fixedURootMatrixEntry g₀ 1 0) ∧
      Int.ModEq (S : ℤ) d (fixedURootMatrixEntry g₀ 1 1) := by
  simp only [← ZMod.intCast_eq_intCast_iff,fixedURootMatrixEntry_cast]
  constructor
  · intro h
    exact ⟨congrArg (fun A : Matrix (Fin 2) (Fin 2) (ZMod S) => A 0 0) h,
      congrArg (fun A : Matrix (Fin 2) (Fin 2) (ZMod S) => A 0 1) h,
      congrArg (fun A : Matrix (Fin 2) (Fin 2) (ZMod S) => A 1 0) h,
      congrArg (fun A : Matrix (Fin 2) (Fin 2) (ZMod S) => A 1 1) h⟩
  · rintro ⟨hu,hc,hv,hd⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simpa using (by assumption)

/-- The literal root-box set for a prescribed special-linear matrix. -/
noncomputable def fixedURootMatrixBoxPoints {S : ℕ}
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (A B α β C D : ℝ) (lcU rcU lcC rcC lcV rcV : Bool) : Finset (Σ _u : ℤ, ℤ × ℤ) :=
  fixedURootBoxPoints S (fixedURootMatrixEntry g₀ 0 0) (fixedURootMatrixEntry g₀ 0 1)
    (fixedURootMatrixEntry g₀ 1 0) (fixedURootMatrixEntry g₀ 1 1)
    A B α β C D lcU rcU lcC rcC lcV rcV

end ArtinMatthews
