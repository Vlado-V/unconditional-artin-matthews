module

public import ArtinMatthews.GiantComparisonStripUnmasked
public import ArtinMatthews.GiantComparisonCutoffActual


set_option backward.privateInPublic true
@[expose] public section

/-! A fixed upper support bound for the smooth cutoff makes the global
physical position tests redundant. The genuine subpower dilation bound
applies to the same copied and auxiliary labels used by the quotient. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantComparisonPositionGuards_of_support {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell N : ℕ} {C : J → Finset (Fin k)}
    (hP : ∀ j p, p ∈ P j → p.Prime)
    {x T : ℝ} (hx : 1 ≤ x) (hroot : T+1 ≤ Real.sqrt x)
    {Ψ : ℝ → ℂ} (hsupp : Function.support Ψ ⊆ Set.Iic T)
    {aux : GiantTwoSidedPatternAuxiliary P C} (a : GiantComparisonUnmaskedEdge P C ell N aux)
    (hD : ((giantComparisonSharedProduct a.val.1*giantTwoSidedPatternAuxiliaryProduct aux:ℕ):ℝ) ≤
      Real.sqrt x)
    (hΨ : Ψ ((a.val.2.1.val:ℝ)/(x*(giantTwoSidedPatternAuxiliaryProduct aux:ℝ))) ≠ 0) :
    GiantComparisonPositionGuards (Ioc 0 ⌊x^2⌋₊) (Ioc 0 ⌊x^2⌋₊) aux a.val := by
  let D := giantComparisonSharedProduct a.val.1
  let d := giantTwoSidedPatternAuxiliaryProduct aux
  let w := a.val.2.1.val
  have hDpos : 0 < D := giantComparisonSharedProduct_pos hP a.val.1
  have hdpos : 0 < d :=
    prod_pos fun j _ => prod_pos fun i _ => (hP j _ (aux j i).property).pos
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hw : 0 < w := (mem_Ioc.mp a.val.2.1.property).1
  have hcut : (w:ℝ)/(x*(d:ℝ)) ≤ T := hsupp hΨ
  have hwle := (div_le_iff₀ (mul_pos hx0 (Nat.cast_pos.mpr hdpos))).mp hcut
  have hshift : T*x+1 ≤ x*Real.sqrt x := calc
    _ ≤ x*(T+1) := by nlinarith only [hx]
    _ ≤ _ := mul_le_mul_of_nonneg_left hroot hx0.le
  have ht : ((D*(w+d):ℕ):ℝ) ≤ x^2 := by
    push_cast
    calc
      (D:ℝ)*((w:ℝ)+(d:ℝ)) ≤ (D:ℝ)*(T*(x*(d:ℝ))+(d:ℝ)) :=
        mul_le_mul_of_nonneg_left (add_le_add hwle le_rfl) (Nat.cast_nonneg _)
      _ = (T*x+1)*((D*d:ℕ):ℝ) := by push_cast; ring
      _ ≤ (x*Real.sqrt x)*Real.sqrt x :=
        mul_le_mul hshift hD (Nat.cast_nonneg _) (mul_nonneg hx0.le (Real.sqrt_nonneg _))
      _ = x^2 := by rw [mul_assoc, Real.mul_self_sqrt hx0.le, pow_two]
  have ht' : D*(w+d) ≤ ⌊x^2⌋₊ := Nat.le_floor ht
  exact ⟨mem_Ioc.mpr ⟨Nat.mul_pos hDpos hw,
      (Nat.mul_le_mul_left D (Nat.le_add_right w d)).trans ht'⟩,
    mem_Ioc.mpr ⟨Nat.mul_pos hDpos (by omega), ht'⟩⟩

theorem giantCandidateComparisonCutoff_eq_unmasked_eventually {I : Type*} [Fintype I]
    (e : I → ℝ) (he : ∀ i, e i ≤ 1/5) {ε : ℝ} (hεq : ε < 1/4)
    {m : ℕ} (hm : 0 < m) (χ : DirichletCharacter ℂ m) (γ : ℝ) (j k : ℕ)
    (q : ℝ) {Ψ : ℝ → ℂ} {T : ℝ} (hT : 0 < T) (hsupp : Function.support Ψ ⊆ Set.Iic T) :
    ∀ᶠ x : ℝ in atTop, ∀ (S : Finset (GiantCandidateGroupIndex x)) (C : S → Finset (Fin k)),
      let P (g : S) := giantCandidateGroup x g.val
      ∀ K : GiantTwoSidedPatternCoefficient P C 1,
      let F := giantCandidateFirstEndpoint e ε x
      let G := giantCandidateAllocationCore (giantCandidateFullPrimes x) (univ.biUnion P)
        (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j
      giantTwoSidedPhysicalPatternCutoffPairing (Z:=Ioc 0 ⌊x^2⌋₊) C 1 q 0
          (giantComparisonCharacterCoefficient χ K) Ψ x
          (fun n => (giantTwoSidedEndpointDamping P (k+1) q n : ℂ)*conj (F n))
          (fun t => (giantTwoSidedEndpointDamping P (k+1) q t.val.1.val : ℂ)*
            χ t.val.1.val*G t.val.1.val) =
        ∑ aux : GiantTwoSidedPatternAuxiliary P C,
        ∑ a : GiantComparisonUnmaskedEdge P C 1 ⌊x^2⌋₊ aux,
          giantComparisonUnmaskedSummand x q Ψ χ F G K a := by
  filter_upwards [giantCandidateComparisonCutoff_eq_shared_eventually e he hεq hm χ γ j q Ψ,
    giantCandidatePatternDilation_subpower k (δ:=1/2) (by norm_num),
    giantCandidateFullPrimes_prime_upper_eventually, eventually_ge_atTop (1:ℝ),
    eventually_ge_atTop ((T+1)^2)] with x hs hD hp hx hxT
  intro S C
  dsimp only
  intro K
  let P (g : S) := giantCandidateGroup x g.val
  let U := Ioc 0 ⌊x^2⌋₊
  have hP (g : S) (p : ℕ) (hp' : p ∈ P g) : p.Prime :=
    (hp p (mem_giantCandidateFullPrimes.mpr ⟨g.val,hp'⟩)).1
  have hroot : T+1 ≤ Real.sqrt x :=
    (Real.le_sqrt (by positivity) (zero_le_one.trans hx)).mpr hxT
  rw [hs S k ⌊x^2⌋₊ U (Subset.refl _) C K]
  apply sum_congr rfl
  intro aux _
  apply giantComparisonShared_sum_unmasked x q Ψ χ _ _ K aux
  intro a ha
  have h := hD S 1 C (giantComparisonJoinLabels a.val.1 a.val.2.2.1) aux
  rw [giantTwoSidedPatternDilation, giantComparisonSharedProduct_join, ← Real.sqrt_eq_rpow] at h
  exact giantComparisonPositionGuards_of_support hP hx hroot hsupp a h ha

end
end ArtinMatthews
