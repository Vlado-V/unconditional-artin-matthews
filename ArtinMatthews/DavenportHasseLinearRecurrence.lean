module

public import ArtinMatthews.DavenportHasseMonicFrames
public import ArtinMatthews.DavenportHasseCoefficientCollapse


set_option backward.privateInPublic true
@[expose] public section

/-! The scalar Newton recurrence for a series 1+G T has the exact
Davenport--Hasse sign. The actual polynomial recurrence is supplied by
the factorization theorem in the final application. -/
namespace ArtinMatthews.DavenportHasse
open scoped BigOperators
noncomputable section

def linearCoefficient (G : ℂ) (n : ℕ) : ℂ :=
  if n=0 then 1 else if n=1 then G else 0

theorem degreeCoefficient_linear {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (hχ : χ ≠ 1) (ψ : AddChar F ℂ) (n : ℕ) :
    degreeCoefficient χ ψ n = linearCoefficient (gaussSum χ ψ) n :=
  degreeCoefficient_eq χ hχ ψ n

theorem linearCoefficient_convolution (G : ℂ) (b : ℕ → ℂ) (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 (n+2), b k * linearCoefficient G (n+2-k)) =
      b (n+1)*G+b (n+2) := by
  rw [Finset.sum_Icc_succ_top (a := 1) (b := n+1) (by omega),
    Finset.sum_Icc_succ_top (a := 1) (b := n) (by omega)]
  have hz : (∑ k ∈ Finset.Icc 1 n, b k * linearCoefficient G (n+2-k)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    have h0 : n+2-k ≠ 0 := by omega
    have h1 : n+2-k ≠ 1 := by omega
    simp only [linearCoefficient,ite_eq_right h0,ite_eq_right h1,mul_zero]
  have hsub : n+2-(n+1)=1 := by omega
  rw [hz,hsub,Nat.sub_self]
  simp only [linearCoefficient,Nat.one_ne_zero,ite_false,ite_true,Nat.zero_ne_one,mul_one,zero_add]

theorem linearCoefficient_recurrence_solution (G : ℂ) (b : ℕ → ℂ)
    (hb : ∀ n : ℕ, (n : ℂ)*linearCoefficient G n =
      ∑ k ∈ Finset.Icc 1 n, b k*linearCoefficient G (n-k)) (n : ℕ) :
    b (n+1) = (-1 : ℂ)^n * G^(n+1) := by
  induction n with
  | zero =>
      have h := hb 1
      simpa [linearCoefficient] using h.symm
  | succ n ih =>
      have h := hb (n+2)
      have h0 : linearCoefficient G (n+2)=0 := by simp [linearCoefficient]
      rw [h0,mul_zero,linearCoefficient_convolution] at h
      have hstep : b (n+2) = -b (n+1)*G := by linear_combination -h
      rw [show n.succ+1=n+2 by omega,hstep,ih]
      rw [pow_succ (-1 : ℂ) n,pow_succ G (n+1)]
      ring

end
end ArtinMatthews.DavenportHasse
