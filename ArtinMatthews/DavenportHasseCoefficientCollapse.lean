module

public import ArtinMatthews.DavenportHasseMonicFrames


set_option backward.privateInPublic true
@[expose] public section

/-! The complete degree-layer sum of the actual polynomial character
weight is linear: constant coefficient 1, linear coefficient the Gauss
sum, and all higher coefficients vanish. -/
namespace ArtinMatthews.DavenportHasse
open Polynomial
open scoped Classical BigOperators
noncomputable section
variable {F : Type*} [Field F] [Fintype F]

theorem degreeCoefficient_zero (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    degreeCoefficient χ ψ 0 = 1 := by
  simp [degreeCoefficient,monicFrame,Polynomial.ofFn_zero',polynomialWeight_one]

omit [Fintype F] in
theorem monicFrame_weight_one (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (c : F) (a : Fin 0 → F) :
    polynomialWeight χ ψ (monicFrame 1 (Fin.cons c a)) = χ (-c)*ψ (-c) := by
  rw [monicFrame_weight χ ψ 0]
  simp only [zero_add,pow_one,neg_one_mul,Fin.cons_zero,Fin.last_zero]

theorem degreeCoefficient_one (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    degreeCoefficient χ ψ 1 = gaussSum χ ψ := by
  calc
    _ = ∑ t : F × (Fin 0 → F), polynomialWeight χ ψ
        (monicFrame 1 ((Fin.consEquiv (fun _ : Fin 1 => F)) t)) :=
      ((Fin.consEquiv (fun _ : Fin 1 => F)).sum_comp _).symm
    _ = ∑ c : F, χ (-c)*ψ (-c) := by
      rw [Fintype.sum_prod_type]
      change (∑ c : F, ∑ a : Fin 0 → F, polynomialWeight χ ψ (monicFrame 1 (Fin.cons c a))) = _
      simp only [monicFrame_weight_one,
        Finset.sum_const,Finset.card_univ,Fintype.card_unique,one_nsmul]
    _ = _ := Equiv.sum_comp (Equiv.neg F) (fun c => χ c*ψ c)

omit [Fintype F] in
theorem monicFrame_weight_cons (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (n : ℕ) (c : F) (a : Fin (n+1) → F) :
    polynomialWeight χ ψ (monicFrame (n+2) (Fin.cons c a)) =
      χ ((-1 : F)^(n+2)*c)*ψ (-a (Fin.last n)) := by
  rw [monicFrame_weight χ ψ (n+1)]
  have hlast : (Fin.last (n+1) : Fin (n+2)) = (Fin.last n).succ := rfl
  simp only [Fin.cons_zero,hlast,Fin.cons_succ]

theorem degreeCoefficient_add_two (χ : MulChar F ℂ) (hχ : χ ≠ 1)
    (ψ : AddChar F ℂ) (n : ℕ) : degreeCoefficient χ ψ (n+2) = 0 := by
  have hz : ∑ c : F, χ c = 0 := MulChar.sum_eq_zero_of_ne_one hχ
  calc
    _ = ∑ t : F × (Fin (n+1) → F), polynomialWeight χ ψ
        (monicFrame (n+2) ((Fin.consEquiv (fun _ : Fin (n+2) => F)) t)) :=
      ((Fin.consEquiv (fun _ : Fin (n+2) => F)).sum_comp _).symm
    _ = ∑ c : F, ∑ a : Fin (n+1) → F,
        χ ((-1 : F)^(n+2)*c)*ψ (-a (Fin.last n)) := by
      rw [Fintype.sum_prod_type]
      change (∑ c : F, ∑ a : Fin (n+1) → F,
        polynomialWeight χ ψ (monicFrame (n+2) (Fin.cons c a))) = _
      simp only [monicFrame_weight_cons]
    _ = ∑ a : Fin (n+1) → F, ∑ c : F,
        χ ((-1 : F)^(n+2)*c)*ψ (-a (Fin.last n)) := Finset.sum_comm
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      simp only [map_mul]
      rw [← Finset.sum_mul,← Finset.mul_sum,hz,mul_zero,zero_mul]

theorem degreeCoefficient_eq (χ : MulChar F ℂ) (hχ : χ ≠ 1) (ψ : AddChar F ℂ) (n : ℕ) :
    degreeCoefficient χ ψ n = if n=0 then 1 else if n=1 then gaussSum χ ψ else 0 := by
  rcases n with _ | (_ | n)
  · simp only [degreeCoefficient_zero,ite_true]
  · simp only [Nat.zero_add,degreeCoefficient_one,Nat.one_ne_zero,ite_false,ite_true]
  · rw [degreeCoefficient_add_two χ hχ ψ n]
    simp

end
end ArtinMatthews.DavenportHasse
