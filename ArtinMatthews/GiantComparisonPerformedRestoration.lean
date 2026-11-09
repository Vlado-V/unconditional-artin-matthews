module

public import ArtinMatthews.GiantComparisonCutoffRestoration
public import ArtinMatthews.GiantComparisonCutoffActual


set_option backward.privateInPublic true
@[expose] public section

/-! The signed nonempty comparison uses the two actual character-cell
kernels. The independent-list expression keeps them and the auxiliary
law unchanged, with the source collision error proved quantitatively. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable

def giantCandidatePerformedFreeCoefficient {x : ℝ}
    (S : Finset (GiantCandidateGroupIndex x)) {k ell : ℕ}
    (A B : Finset (GiantCandidatePerformedBig S × Fin k)) (Q : ℕ) (h ξ : ℝ) :
    GiantComparisonListCoefficient (fun g : S => giantCandidateGroup x g.val)
      (giantCandidatePerformedPattern S (idealResidualCopied (some (A,B)))) ell :=
  fun b b' aux =>
    let f (g : GiantCandidatePerformedBig S) := giantCandidatePerformedSplitEquiv S (.inr g)
    giantComparisonFreeCoefficient (P:=giantCandidatePerformedBigBand S) (ell:=ell) A B Q h ξ
      (fun g => b (f g)) (fun g => b' (f g)) (fun g => aux (f g))

theorem giantCandidatePerformedFreeCoefficient_norm_le {x : ℝ}
    (S : Finset (GiantCandidateGroupIndex x)) {k ell : ℕ}
    (A B : Finset (GiantCandidatePerformedBig S × Fin k)) (Q : ℕ) (h : ℝ)
    {ξ : ℝ} (hξ : 0 < ξ) :
    let P (g : S) := giantCandidateGroup x g.val
    let C := giantCandidatePerformedPattern S (idealResidualCopied (some (A,B)))
    ∀ (b b' : GiantComparisonFreeLabels P C ell) (aux : GiantTwoSidedPatternAuxiliary P C),
      ‖giantCandidatePerformedFreeCoefficient S A B Q h ξ b b' aux‖ ≤ (((Q:ℝ)^2)/ξ)^2 := by
  dsimp only
  intro b b' aux
  rw [pow_two (((Q:ℝ)^2)/ξ)]
  simp only [giantCandidatePerformedFreeCoefficient,giantComparisonFreeCoefficient,
    norm_mul,norm_neg,norm_pow,norm_one,one_pow,one_mul]
  exact mul_le_mul (idealCharacterCellKernel_norm_le _ Q h hξ _ _)
    (idealCharacterCellKernel_norm_le _ Q h hξ _ _) (norm_nonneg _)
    (div_nonneg (sq_nonneg _) hξ.le)

theorem giantCandidatePerformedComparisonCutoff_restored_eventually {I : Type*} [Fintype I]
    (e : I → ℝ) (he : ∀ i, 0 < e i ∧ e i ≤ 1/5) {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4)
    {m : ℕ} (hm : 0 < m) (χ : DirichletCharacter ℂ m)
    {γ : ℝ} (hγ : 0 < γ) (j : ℕ) (hj : 0 < j) (k : ℕ)
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (Ψ : ℝ → ℂ)
    {a b BΨ : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hΨ : ∀ y ∉ Set.Icc a b, Ψ y = 0) (hBΨ : ∀ y, ‖Ψ y‖ ≤ BΨ) (E : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (S : Finset (GiantCandidateGroupIndex x))
        (A B : Finset (GiantCandidatePerformedBig S × Fin k)) (Q : ℕ) (h ξ : ℝ), 0 < ξ →
      let P (g : S) := giantCandidateGroup x g.val
      let C₀ := giantCandidatePerformedPattern S (idealResidualCopied (some (A,B)))
      let K : GiantTwoSidedPatternCoefficient P C₀ 1 := giantCandidatePerformedCoefficient S
        (idealResidualCoefficient (giantCandidatePerformedBigBand S) Q h ξ (some (A,B)))
      let L : GiantComparisonListCoefficient P C₀ 1 :=
        giantCandidatePerformedFreeCoefficient S A B Q h ξ
      let F := giantCandidateFirstEndpoint e ε x
      let G := giantCandidateAllocationCore (giantCandidateFullPrimes x) (univ.biUnion P)
        (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j
      ‖giantTwoSidedPhysicalPatternCutoffPairing (Z:=Ioc 0 ⌊x^2⌋₊) C₀ 1 q 0
          (giantComparisonCharacterCoefficient χ K) Ψ x
          (fun n => (giantTwoSidedEndpointDamping P (k+1) q n : ℂ)*conj (F n))
          (fun t => (giantTwoSidedEndpointDamping P (k+1) q t.val.1.val : ℂ)*
            χ t.val.1.val*G t.val.1.val) -
        (∑ aux : GiantTwoSidedPatternAuxiliary P C₀,
          giantComparisonIndependentAuxiliarySum ⌊x^2⌋₊ x q Ψ χ F G L aux)‖ ≤
        C*(((Q:ℝ)^2)/ξ)^2*(Real.log x)^(-E) := by
  obtain ⟨C,hC,hbound⟩ := giantCandidateComparisonCutoff_independent_eventually
    e he hε hεq hm χ hγ j hj k hq hq1 Ψ ha hb hΨ hBΨ E
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with x hx
  intro S A B Q h ξ hξ
  exact hx S (idealResidualCopied (some (A,B))) _ _ ((((Q:ℝ)^2)/ξ)^2)
    (sq_nonneg _) (fun c b b' aux => giantCandidatePerformedComparisonCoefficient_join_free S A B Q h ξ c b b' aux)
    (giantCandidatePerformedFreeCoefficient_norm_le S (ell:=1) A B Q h hξ)

end
end ArtinMatthews
