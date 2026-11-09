module

public import ArtinMatthews.SourceReflectionPowerful


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField
open scoped NumberField Classical
noncomputable section

private def halfExponents {ι : Type*} (e : ι →₀ ℕ) : ι →₀ ℕ :=
  e.mapRange (fun n => n / 2) (by decide)

private def exponentSquarePartsEquiv (ι : Type*) :
    (ι →₀ ℕ) ≃ {e : ι →₀ ℕ // sourceReflectionIsSquarefree e} × (ι →₀ ℕ) where
  toFun e := (⟨sourceReflectionParity e, sourceReflectionParity_squarefree e⟩, halfExponents e)
  invFun p := p.1.val + 2 • p.2
  left_inv e := by
    ext P
    simp only [sourceReflectionParity, halfExponents, Finsupp.mapRange_apply, Finsupp.add_apply,
      Finsupp.smul_apply, Nat.nsmul_eq_mul]
    omega
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      ext P
      simp only [sourceReflectionParity, Finsupp.mapRange_apply, Finsupp.add_apply,
        Finsupp.smul_apply, Nat.nsmul_eq_mul]
      have h := p.1.property P
      omega
    · ext P
      simp only [halfExponents, Finsupp.mapRange_apply, Finsupp.add_apply,
        Finsupp.smul_apply, Nat.nsmul_eq_mul]
      have h := p.1.property P
      omega

variable (F : Type) [Field F] [NumberField F]

private def squarefreeExponentEquiv :
    {e : ProbePrime F →₀ ℕ // sourceReflectionIsSquarefree e} ≃
      {I : Ideal (𝓞 F) // Squarefree I} where
  toFun e := ⟨sourceFullExponentIdeal F e.val, (sourceFullExponentIdeal_squarefree_iff F _).2 e.property⟩
  invFun I := ⟨sourceFullIdealExponents F I.val, (sourceFullExponentIdeal_squarefree_iff F _).1
    (by rw [sourceFullIdealExponents_recover F I.val I.property.ne_zero]; exact I.property)⟩
  left_inv e := Subtype.ext ((sourceFullExponentIdealEquiv F).left_inv e.val)
  right_inv I := Subtype.ext (sourceFullIdealExponents_recover F I.val I.property.ne_zero)

/-- Unique squarefree-times-square factorization of the nonzero integral ideals. -/
def sourceQuadraticIdealSquareParts :
    {I : Ideal (𝓞 F) // I ≠ ⊥} ≃
      {I : Ideal (𝓞 F) // Squarefree I} × {I : Ideal (𝓞 F) // I ≠ ⊥} :=
  (sourceFullExponentIdealEquiv F).symm.trans
    ((exponentSquarePartsEquiv (ProbePrime F)).trans
      ((squarefreeExponentEquiv F).prodCongr (sourceFullExponentIdealEquiv F)))

theorem sourceQuadraticIdealSquareParts_symm_val
    (p : {I : Ideal (𝓞 F) // Squarefree I} × {I : Ideal (𝓞 F) // I ≠ ⊥}) :
    ((sourceQuadraticIdealSquareParts F).symm p).val = p.1.val * p.2.val ^ 2 := by
  change sourceFullExponentIdeal F
    (sourceFullIdealExponents F p.1.val + 2 • sourceFullIdealExponents F p.2.val) = _
  rw [sourceFullExponentIdeal_add, sourceFullExponentIdeal_nsmul,
    sourceFullIdealExponents_recover F _ p.1.property.ne_zero,
    sourceFullIdealExponents_recover F _ p.2.property]

theorem sourceQuadraticIdealSquareParts_val (I : {I : Ideal (𝓞 F) // I ≠ ⊥}) :
    ((sourceQuadraticIdealSquareParts F I).1.val) *
      ((sourceQuadraticIdealSquareParts F I).2.val) ^ 2 = I.val := by
  rw [← sourceQuadraticIdealSquareParts_symm_val, Equiv.symm_apply_apply]

end
end ArtinMatthews.SourceEulerAssembly
