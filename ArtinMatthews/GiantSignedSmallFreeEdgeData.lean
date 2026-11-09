module

public import ArtinMatthews.GiantSignedEdgeWeakColumn
public import ArtinMatthews.GiantSignedSmallEdgeKernel


set_option backward.privateInPublic true
@[expose] public section

/-! The literal small/free edge and its unrestricted row and positivity identities. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantSignedEdgeApply_ofReal_eq_norm {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} [∀ j, ∀ p : P j, NeZero p.val] {t : J → ℕ}
    (ν : (j : J) → P j → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    (V : J → ℝ) (hV : ∀ j, 0 ≤ V j) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (d : ℤ) (D : ℕ) (source : GiantSignedPrimeTuple P t)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℝ)
    (hf : ∀ target out, 0 ≤ f target out) (m : GiantSignedMemory P) :
    giantSignedEdgeApply (fun j p => (ν j p : ℂ)) V ρ d D source
      (fun target out => (f target out : ℂ)) m =
      (‖giantSignedEdgeApply (fun j p => (ν j p : ℂ)) V ρ d D source
        (fun target out => (f target out : ℂ)) m‖ : ℂ) := by
  apply Complex.ext
  · simpa only [Complex.ofReal_re] using
      (giantSignedEdgeApply_ofReal_norm ν hν V hV hρ d D f hf source m).symm
  · rw [giantSignedEdgeApply_eq_coe_coupled]
    rfl

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ} {t : B → ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]

def giantSignedSmallPrefixProduct (s : GiantTwoSidedResidueState PS (k+ell)) : ℕ :=
  ∏ g : S, ∏ i : Fin k, (s.val.2 g (Fin.castAdd ell i)).val

def giantSignedSmallFreeEdgeApply (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (κ : ℤ) (q ρ : ℝ) (D : ℕ)
    (f : GiantTwoSidedResidueState PS (k+ell) → GiantSignedPrimeTuple PB t →
      GiantSignedMemory PB → ℂ)
    (s : GiantTwoSidedResidueState PS (k+ell)) (a : GiantSignedPrimeTuple PB t)
    (m : GiantSignedMemory PB) : ℂ :=
  ∑ z : GiantTwoSidedResidueState PS (k+ell), (giantSignedSmallEdgeWeight κ D q s z : ℂ) *
    giantSignedEdgeApply (fun g p => (ν g p : ℂ)) V ρ
      (κ * ((giantSignedSmallPrefixProduct s * D : ℕ) : ℤ))
      (giantSignedSmallPrefixProduct s * D) a (f z) m

omit [∀ g, ∀ p : PB g, NeZero p.val] in
theorem giantSignedSmallFreeEdgeApply_row_bound
    (hPS : ∀ j p, p ∈ PS j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    {vmin massMax q ρ U u BS : ℝ}
    (hvmin : 0 < vmin) (hV : ∀ g, vmin ≤ V g)
    (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ massMax)
    (hq : 0 < q) (hq1 : q ≤ 1) (hBS : 0 ≤ BS)
    (hbudget : ∀ j (z : ℕ),
      (bandReciprocalMass (PS j))⁻¹ ^ ell * ((z : ℝ) + (ell : ℝ)) ^ ell *
        q ^ ((z : ℝ) / 2) ≤ BS)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hU : 0 ≤ U) (hu : 1 ≤ u)
    (tmax : ℕ) (ht : ∀ g, t g ≤ tmax) (κ : ℤ) (D : ℕ)
    (f : GiantTwoSidedResidueState PS (k+ell) → GiantSignedPrimeTuple PB t →
      GiantSignedMemory PB → ℂ)
    (hf : ∀ s a m, ‖f s a m‖ ≤ U * u ^ (∑ g, m.1 g))
    (s : GiantTwoSidedResidueState PS (k+ell)) (a : GiantSignedPrimeTuple PB t)
    (m : GiantSignedMemory PB) :
    ‖giantSignedSmallFreeEdgeApply ν V κ q ρ D f s a m‖ ≤
      U * u ^ (∑ g, m.1 g) *
        (giantSignedEdgeUniformConstant ρ u vmin⁻¹ massMax tmax) ^ Fintype.card B *
          BS ^ Fintype.card S := by
  let K := U * u ^ (∑ g, m.1 g) *
    (giantSignedEdgeUniformConstant ρ u vmin⁻¹ massMax tmax) ^ Fintype.card B
  have hK : 0 ≤ K := mul_nonneg
    (mul_nonneg hU (pow_nonneg (le_trans zero_le_one hu) _))
    (pow_nonneg (giantSignedEdgeUniformConstant_nonneg hρ1 (le_trans zero_le_one hu)) _)
  have hrow (z : GiantTwoSidedResidueState PS (k+ell)) :
      ‖giantSignedEdgeApply (fun g p => (ν g p : ℂ)) V ρ
        (κ * ((giantSignedSmallPrefixProduct s * D : ℕ) : ℤ))
        (giantSignedSmallPrefixProduct s * D) a (f z) m‖ ≤ K :=
    giantSignedEdgeApply_row_bound ν hν V hvmin hV hMass hρ hρ1 hu hU tmax ht
      (κ * ((giantSignedSmallPrefixProduct s * D : ℕ) : ℤ))
      (giantSignedSmallPrefixProduct s * D) a (f z) (hf z) m
  unfold giantSignedSmallFreeEdgeApply
  calc
    _ ≤ ∑ z : GiantTwoSidedResidueState PS (k+ell), giantSignedSmallEdgeWeight κ D q s z * K := by
      apply norm_sum_le_of_le
      intro z _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (giantSignedSmallEdgeWeight_nonneg κ D q s z)]
      exact mul_le_mul_of_nonneg_left (hrow z) (giantSignedSmallEdgeWeight_nonneg κ D q s z)
    _ = K * ∑ z : GiantTwoSidedResidueState PS (k+ell), giantSignedSmallEdgeWeight κ D q s z := by
      rw [← Finset.sum_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (giantSignedSmallEdgeWeight_row hPS hdis hVS κ D hq hq1 hBS hbudget s) hK

theorem giantSignedSmallFreeEdgeApply_ofReal_norm
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (V : B → ℝ) (hV : ∀ g, 0 ≤ V g) (κ : ℤ) (q : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) (D : ℕ)
    (f : GiantTwoSidedResidueState PS (k+ell) → GiantSignedPrimeTuple PB t →
      GiantSignedMemory PB → ℝ) (hf : ∀ s a m, 0 ≤ f s a m)
    (s : GiantTwoSidedResidueState PS (k+ell)) (a : GiantSignedPrimeTuple PB t)
    (m : GiantSignedMemory PB) :
    ‖giantSignedSmallFreeEdgeApply ν V κ q ρ D (fun z b out => (f z b out : ℂ)) s a m‖ =
      ∑ z : GiantTwoSidedResidueState PS (k+ell), giantSignedSmallEdgeWeight κ D q s z *
        ‖giantSignedEdgeApply (fun g p => (ν g p : ℂ)) V ρ
          (κ * ((giantSignedSmallPrefixProduct s * D : ℕ) : ℤ))
          (giantSignedSmallPrefixProduct s * D) a (fun b out => (f z b out : ℂ)) m‖ := by
  unfold giantSignedSmallFreeEdgeApply
  have he (z : GiantTwoSidedResidueState PS (k+ell)) :=
    giantSignedEdgeApply_ofReal_eq_norm ν hν V hV hρ
      (κ * ((giantSignedSmallPrefixProduct s * D : ℕ) : ℤ))
      (giantSignedSmallPrefixProduct s * D) a (f z) (hf z) m
  have hs : (∑ z : GiantTwoSidedResidueState PS (k+ell),
      (giantSignedSmallEdgeWeight κ D q s z : ℂ) *
        giantSignedEdgeApply (fun g p => (ν g p : ℂ)) V ρ
          (κ * ((giantSignedSmallPrefixProduct s * D : ℕ) : ℤ))
          (giantSignedSmallPrefixProduct s * D) a (fun b out => (f z b out : ℂ)) m) =
      ((∑ z : GiantTwoSidedResidueState PS (k+ell), giantSignedSmallEdgeWeight κ D q s z *
        ‖giantSignedEdgeApply (fun g p => (ν g p : ℂ)) V ρ
          (κ * ((giantSignedSmallPrefixProduct s * D : ℕ) : ℤ))
          (giantSignedSmallPrefixProduct s * D) a (fun b out => (f z b out : ℂ)) m‖ : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sum, Complex.ofReal_mul]
    apply Finset.sum_congr rfl
    intro z _
    exact congrArg (fun x : ℂ => (giantSignedSmallEdgeWeight κ D q s z : ℂ) * x) (he z)
  rw [hs, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (Finset.sum_nonneg (fun z _ => mul_nonneg
    (giantSignedSmallEdgeWeight_nonneg κ D q s z) (norm_nonneg _)))


end
end ArtinMatthews
