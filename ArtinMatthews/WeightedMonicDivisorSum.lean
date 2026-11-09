module

public import ArtinMatthews.WeightedMonicDivision
public import ArtinMatthews.WeightedMonicPointing


set_option backward.privateInPublic true
@[expose] public section

/-! Sum a multiplicative polynomial weight over a monic degree layer
divisible by a fixed monic polynomial. The quotient parametrization is
the proved divisor equivalence, not an assumed counting formula. -/
namespace ArtinMatthews.WeightedMonic
open Polynomial
open scoped Classical BigOperators
noncomputable section
variable {F : Type*} [Field F] [Fintype F] {k n : ℕ}

theorem divisor_weight_sum (w : F[X] → ℂ)
    (hm : ∀ P Q, P.Monic → Q.Monic → w (P*Q)=w P*w Q)
    (P : MonicDegreeEq F k) (hkn : k ≤ n) :
    (∑ Q ∈ layer n, if P.1 ∣ Q then w Q else 0) = w P.1 * coefficient w (n-k) := by
  have hs : (∑ Q ∈ layer n, if P.1 ∣ Q then w Q else 0) =
      ∑' Q : DivisibleLayer P n, w Q.1.1 := by
    rw [← coefficient_sum]
    unfold coefficient
    symm
    simpa only [DivisibleLayer,Set.coe_ofPred,Set.indicator_apply,Set.mem_ofPred_eq] using
      (tsum_subtype {Q : MonicDegreeEq F n | P.1 ∣ Q.1} (fun Q => w Q.1))
  have he := (divisorEquiv P hkn).tsum_eq (fun Q : DivisibleLayer P n => w Q.1.1)
  calc
    _ = ∑' Q : DivisibleLayer P n, w Q.1.1 := hs
    _ = ∑' R : MonicDegreeEq F (n-k), w (P.1*R.1) := by
      simpa only [divisorEquiv_apply] using he.symm
    _ = ∑' R : MonicDegreeEq F (n-k), w P.1*w R.1 := by
      apply tsum_congr
      intro R
      exact hm P.1 R.1 P.monic R.monic
    _ = w P.1 * coefficient w (n-k) := by rw [tsum_mul_left]; rfl

end
end ArtinMatthews.WeightedMonic
