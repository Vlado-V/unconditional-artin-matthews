module

public import ArtinMatthews.QuadraticRootSign
public import ClassFieldTheory.AlgebraicNumberTheory.PowerResidueSymbols.FiniteField


set_option backward.privateInPublic true
@[expose] public section

/-! The reciprocity power-residue symbol has the same canonical complex sign
as the actual quadratic multiplicative character. -/

namespace ArtinMatthews.QuadraticGauss

open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [Fintype F]

theorem rootSign_powerResidue (hF : ringChar F ≠ 2)
    (hdiv : ((2 : ℕ+) : ℕ) ∣ Fintype.card F - 1) (u : Fˣ) :
    rootSign F (finiteFieldPowerResidueSymbol F 2 hdiv u) =
      residueCharacter F (u : F) := by
  let z : rootsOfUnity 2 F := finiteFieldPowerResidueSymbol F 2 hdiv u
  have hhalf : (Fintype.card F - 1) / 2 = Fintype.card F / 2 := by
    have hodd := FiniteField.odd_card_of_char_ne_two hF
    omega
  have hone : z = 1 ↔
      (u : F) ^ (Fintype.card F / 2) = 1 := by
    constructor
    · intro h
      have hv := congrArg (fun z : rootsOfUnity 2 F => ((z : Fˣ) : F)) h
      change (u : F) ^ ((Fintype.card F - 1) / 2) = 1 at hv
      rwa [hhalf] at hv
    · intro h
      apply Subtype.ext
      apply Units.ext
      change (u : F) ^ ((Fintype.card F - 1) / 2) = 1
      rwa [hhalf]
  change (if z = 1 then (1 : ℂ) else -1) = _
  simp only [hone]
  change _ = (quadraticChar F (u : F) : ℂ)
  rw [quadraticChar_eq_pow_of_char_ne_two hF u.ne_zero]
  simp only [Int.cast_ite, Int.cast_one, Int.cast_neg]

end

end ArtinMatthews.QuadraticGauss
