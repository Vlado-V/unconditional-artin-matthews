module

public import ArtinMatthews.CubicThetaCoefficients
public import OAI.NumberTheory.PrimePackets.IdealCoefficients


set_option backward.privateInPublic true
@[expose] public section

/-! Coprime multiplicativity of the actual weighted ideal-norm fibers. -/

noncomputable section
namespace ArtinMatthews

open OAI OAI.SevenEighths
open scoped BigOperators

local notation "EO" => HeckeFamily.O

/-- The finite norm fiber and its predicate-subtype model are the same
actual family of integral ideals. -/
def thetaIdealNormFiberEquiv (n : ℕ) :
    ↥(idealsOfNorm n) ≃ {I : Ideal EO // Ideal.absNorm I = n} where
  toFun I := ⟨I.val, mem_idealsOfNorm.mp I.property⟩
  invFun I := ⟨I.val, mem_idealsOfNorm.mpr I.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Multiplication bijects the genuine ideal norm fibers at coprime
nonzero integer arguments. -/
def thetaIdealNormProductEquiv (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0)
    (hmn : m.Coprime n) :
    (↥(idealsOfNorm m) × ↥(idealsOfNorm n)) ≃ ↥(idealsOfNorm (m*n)) :=
  (Equiv.prodCongr (thetaIdealNormFiberEquiv m) (thetaIdealNormFiberEquiv n)).trans
    ((OAI.PrimeDegreePackets.idealNormProductEquiv HeckeFamily.K m n hm hn hmn).trans
      (thetaIdealNormFiberEquiv (m*n)).symm)

@[simp] theorem thetaIdealNormProductEquiv_coe (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0)
    (hmn : m.Coprime n) (p : ↥(idealsOfNorm m) × ↥(idealsOfNorm n)) :
    ((thetaIdealNormProductEquiv m n hm hn hmn p : ↥(idealsOfNorm (m*n))) : Ideal EO) =
      (p.1 : Ideal EO) * (p.2 : Ideal EO) := rfl

/-- The fiber bijection preserves every actual multiplicative ideal
weight, not only the unweighted ideal count. -/
theorem weighted_idealsOfNorm_mul (w : Ideal EO →*₀ ℂ) {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m.Coprime n) :
    (∑ I ∈ idealsOfNorm (m*n), w I) =
      (∑ I ∈ idealsOfNorm m, w I) * (∑ J ∈ idealsOfNorm n, w J) := by
  classical
  let e := thetaIdealNormProductEquiv m n hm hn hmn
  have hs (k : ℕ) : (∑ I ∈ idealsOfNorm k, w I) =
      ∑ I : ↥(idealsOfNorm k), w (I : Ideal EO) :=
    (Finset.sum_coe_sort (idealsOfNorm k) (fun I : Ideal EO => w I)).symm
  rw [hs (m*n), hs m, hs n]
  calc
    _ = ∑ p : ↥(idealsOfNorm m) × ↥(idealsOfNorm n), w (e p : Ideal EO) :=
      (e.bijective.sum_comp (fun I : ↥(idealsOfNorm (m*n)) => w (I : Ideal EO))).symm
    _ = ∑ p : ↥(idealsOfNorm m) × ↥(idealsOfNorm n),
        w (p.1 : Ideal EO) * w (p.2 : Ideal EO) := by
      apply Finset.sum_congr rfl
      intro p _
      exact map_mul w _ _
    _ = _ := by
      simp only [Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]

/-- The actual ideal-sum theta coefficient is multiplicative at coprime
integer arguments, including the zero cases. -/
theorem idealThetaCoeff_mul_of_coprime (χ : HeckeFamily.Character) {m n : ℕ}
    (hmn : m.Coprime n) :
    idealThetaCoeff χ (m*n) = idealThetaCoeff χ m * idealThetaCoeff χ n := by
  by_cases hm : m = 0
  · subst m
    simp
  by_cases hn : n = 0
  · subst n
    simp
  exact weighted_idealsOfNorm_mul (thetaIdealCharacter χ) hm hn hmn

/-- The genuine theta coefficients, with their proved zero index. -/
def idealThetaArithmeticFunction (χ : HeckeFamily.Character) : ArithmeticFunction ℂ where
  toFun := idealThetaCoeff χ
  map_zero' := idealThetaCoeff_zero χ

@[simp] theorem idealThetaArithmeticFunction_apply (χ : HeckeFamily.Character) (n : ℕ) :
    idealThetaArithmeticFunction χ n = idealThetaCoeff χ n := rfl

theorem idealThetaArithmeticFunction_isMultiplicative (χ : HeckeFamily.Character) :
    (idealThetaArithmeticFunction χ).IsMultiplicative := by
  refine ⟨idealThetaCoeff_one χ, ?_⟩
  intro m n hmn
  exact idealThetaCoeff_mul_of_coprime χ hmn

end ArtinMatthews
