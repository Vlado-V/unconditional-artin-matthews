module

public import ArtinMatthews.GiantProgressionCharacters
public import OAI.NumberTheory.DirichletL.PrimeCounting.PrimeMass
public import OAI.NumberTheory.DirichletL.PrimeCounting.AnnularPrimeMass


set_option backward.privateInPublic true
@[expose] public section

/-! The actual prime logarithmic mass in a fixed family of unit residues.
The prime number theorem and its smooth annular transfer are reused from
the checked fixed-modulus residue-class PNT. -/
namespace ArtinMatthews
noncomputable section
open Filter ArithmeticFunction MeasureTheory
open scoped BigOperators Topology

def giantUnitPrimeLogCoeff {M : ℕ} (U : Finset (ZMod M)ˣ) (n : ℕ) : ℝ :=
  ∑ a ∈ U, if n.Prime then vonMangoldt.residueClass (a : ZMod M) n else 0

theorem giantUnitPrimeLogCoeff_nonneg {M : ℕ} (U : Finset (ZMod M)ˣ) (n : ℕ) :
    0 ≤ giantUnitPrimeLogCoeff U n := by
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact vonMangoldt.residueClass_nonneg _ _
  · exact le_rfl

theorem giantUnitPrimeLogCoeff_cumsum {M : ℕ} (U : Finset (ZMod M)ˣ) (N : ℕ) :
    cumsum (giantUnitPrimeLogCoeff U) N =
      ∑ a ∈ U, cumsum (fun n => if n.Prime then vonMangoldt.residueClass (a : ZMod M) n else 0) N := by
  unfold cumsum giantUnitPrimeLogCoeff
  rw [Finset.sum_comm]

theorem giantUnitPrimeLogCoeff_chebyshev {M : ℕ} (U : Finset (ZMod M)ˣ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, cumsum (giantUnitPrimeLogCoeff U) N ≤ C*N := by
  classical
  choose C hC using (fun a : (ZMod M)ˣ =>
    OAI.SevenEighths.PNT.residueClass_chebyshev (a : ZMod M))
  refine ⟨∑ a ∈ U, max (C a) 0, Finset.sum_nonneg (fun _ _ => le_max_right _ _), ?_⟩
  intro N
  rw [giantUnitPrimeLogCoeff_cumsum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro a _
  apply le_trans _ ((hC a N).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg N)))
  unfold cumsum
  apply Finset.sum_le_sum
  intro n _
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs]
    exact le_abs_self _
  · exact norm_nonneg _

theorem giantUnitPrimeLogCoeff_mean {M : ℕ} [NeZero M] (U : Finset (ZMod M)ˣ) :
    Tendsto (fun N : ℕ => cumsum (giantUnitPrimeLogCoeff U) N / N) atTop
      (𝓝 ((U.card : ℝ)/M.totient)) := by
  have h := tendsto_finsetSum U (fun a _ =>
    OAI.SevenEighths.PNT.prime_residueClass_ratio_tendsto (a : ZMod M) a.isUnit)
  convert h using 1
  · funext N
    rw [giantUnitPrimeLogCoeff_cumsum, Finset.sum_div]
  · simp only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

def giantUnitPrimeLogAnnular {M : ℕ} (U : Finset (ZMod M)ˣ)
    (Φ : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  OAI.SevenEighths.PNT.AnnularPrimeMass.annularSum (giantUnitPrimeLogCoeff U) Φ a b x

theorem giant_unit_prime_log_annular_mean {M : ℕ} [NeZero M]
    (U : Finset (ZMod M)ˣ) (Φ : ℝ → ℝ) (hΦ : Differentiable ℝ Φ)
    (hderiv : Continuous (deriv Φ)) {a b : ℝ} (ha : 0<a) (hab : a≤b)
    (hΦa : Φ a=0) (hΦb : Φ b=0) :
    Tendsto (fun x : ℝ => giantUnitPrimeLogAnnular U Φ a b x / x) atTop
      (𝓝 ((U.card : ℝ)/M.totient * ∫ t in a..b, Φ t)) := by
  obtain ⟨C,hC,hbound⟩ := giantUnitPrimeLogCoeff_chebyshev U
  exact OAI.SevenEighths.PNT.AnnularPrimeMass.annularSum_div_tendsto
    (giantUnitPrimeLogCoeff_nonneg U) hC hbound (giantUnitPrimeLogCoeff_mean U)
    Φ hΦ hderiv ha hab hΦa hΦb

end
end ArtinMatthews
