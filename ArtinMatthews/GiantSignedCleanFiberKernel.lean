module

public import ArtinMatthews.GiantSignedCleanFiniteSum


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {I G J : Type*} [AddCommGroup G] [Fintype G] [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell : ℕ}

/-- Matrix entry of the actual damped clean operator on a Kronecker input. -/
def giantSignedDampedCleanFiberKernel
    (freshLaw auxLaw : ∀ j, P j → ℝ) (patterns : Finset I)
    (C : I → J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : ∀ v, GiantTwoSidedPatternCoefficient P (C v) ell) (u : G)
    (dIn dOut : G → ℂ) (x : G) (a : MarkedPhysicalMarking P (k + ell))
    (y : G) (b : MarkedPhysicalMarking P (k + ell)) : ℂ := by
  classical
  exact giantSignedDampedCleanFiberApply freshLaw auxLaw patterns C Θ ζ K u dIn dOut
    (fun y' b' => if y' = y ∧ b' = b then 1 else 0) x a

/-- Exact finite matrix expansion of the original operator, with both damping factors. -/
theorem giantSignedDampedCleanFiberApply_eq_sum_kernel
    (freshLaw auxLaw : ∀ j, P j → ℝ) (patterns : Finset I)
    (C : I → J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : ∀ v, GiantTwoSidedPatternCoefficient P (C v) ell) (u : G)
    (dIn dOut : G → ℂ) (f : G → MarkedPhysicalMarking P (k + ell) → ℂ)
    (x : G) (a : MarkedPhysicalMarking P (k + ell)) :
    giantSignedDampedCleanFiberApply freshLaw auxLaw patterns C Θ ζ K u dIn dOut f x a =
      ∑ y : G, ∑ b : MarkedPhysicalMarking P (k + ell),
        giantSignedDampedCleanFiberKernel freshLaw auxLaw patterns C Θ ζ K u dIn dOut x a y b * f y b := by
  classical
  have hdecomp : f = fun y' b' =>
      ∑ z : G × MarkedPhysicalMarking P (k + ell),
        f z.1 z.2 * (if y' = z.1 ∧ b' = z.2 then 1 else 0) := by
    funext y' b'
    rw [Fintype.sum_prod_type]
    symm
    rw [Finset.sum_eq_single y']
    · rw [Finset.sum_eq_single b']
      · simp
      · intro b _ hb
        simp [Ne.symm hb]
      · intro hb
        exact (hb (Finset.mem_univ _)).elim
    · intro y _ hy
      simp [Ne.symm hy]
    · intro hy
      exact (hy (Finset.mem_univ _)).elim
  calc
    _ = giantSignedDampedCleanFiberApply freshLaw auxLaw patterns C Θ ζ K u dIn dOut
        (fun y' b' => ∑ z : G × MarkedPhysicalMarking P (k + ell),
          f z.1 z.2 * (if y' = z.1 ∧ b' = z.2 then 1 else 0)) x a := by rw [← hdecomp]
    _ = ∑ z : G × MarkedPhysicalMarking P (k + ell), f z.1 z.2 *
        giantSignedDampedCleanFiberApply freshLaw auxLaw patterns C Θ ζ K u dIn dOut
          (fun y' b' => if y' = z.1 ∧ b' = z.2 then 1 else 0) x a :=
      giantSignedDampedCleanFiberApply_sum_mul
        (T := G × MarkedPhysicalMarking P (k + ell)) (I := I) (G := G) (J := J)
        (P := P) (k := k) (ell := ell) freshLaw auxLaw patterns C Θ ζ K u dIn dOut
        Finset.univ (fun z => f z.1 z.2)
        (fun z y' b' => if y' = z.1 ∧ b' = z.2 then (1 : ℂ) else 0) x a
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro b _
      exact mul_comm _ _

end
end ArtinMatthews
